#![feature(stmt_expr_attributes, const_fn, box_patterns, slice_patterns)]
#![allow(non_snake_case, non_camel_case_types)]
// Clippy
//#![allow(explicit_iter_loop, explicit_into_iter_loop, float_cmp, cyclomatic_complexity, too_many_arguments)]

// RSTODO: https://github.com/rust-lang/rust/issues/29599
#![feature(plugin)]
#![plugin(interpolate_idents)]
// RSTODO: review how useful mast! is
#![plugin(ayzim_macros)]

// RSTODO: review all numeric casts
// https://github.com/rust-lang/rfcs/pull/1218

#[macro_use] extern crate cfor;
#[macro_use] extern crate lazy_static;
extern crate string_cache;
extern crate serde;
extern crate serde_json;
extern crate odds;
extern crate phf;
extern crate phf_builder;
extern crate smallvec;
extern crate typed_arena;
extern crate libc;
extern crate conv;

use std::env;
use std::fs;
use std::io;
use std::io::{Read, Write};
use std::mem;
#[cfg(feature = "profiling")]
use std::time;

use optimizer::{
    eliminateDeadFuncs,
    eliminate,
    simplifyExpressions,
    optimizeFrounds,
    simplifyIfs,
    registerize,
    registerizeHarder,
    minifyLocals,
    asmLastOpts,
};

const DEBUG: bool = false;

include!(concat!(env!("OUT_DIR"), "/static_atoms.rs"));

// RSTODO: not sure why tt can't be expr in these macros?
macro_rules! isv {
    [ $( $x:tt ),+, ] => { isv![ $( $x ),+ ] };
    [ $( $x:tt ),* ] => { vec![ $( is!($x) ),+ ] };
}

macro_rules! printlnerr {
    ($( $arg:tt )*) => {{
        use std::io::Write;
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    }};
}

trait MoreTime {
    fn to_ms(&self) -> u64;
    fn to_us(&self) -> u64;
}
impl MoreTime for std::time::Duration {
    fn to_ms(&self) -> u64 { self.as_secs()*1_000 + self.subsec_nanos() as u64/1_000_000 }
    fn to_us(&self) -> u64 { self.as_secs()*1_000_000 + self.subsec_nanos() as u64/1_000 }
}

#[macro_use]
pub mod cashew;
pub mod optimizer;
pub mod parser;

mod num {
    use conv::*;
    // https://github.com/rust-lang/rfcs/pull/1218
    // https://doc.rust-lang.org/book/casting-between-types.html#numeric-casts (note UB)

    // RSTODO: carefully review uses of this function - should they use isInteger64?
    pub fn isInteger(x: f64) -> bool {
        assert!(x.is_normal() || x == 0f64);
        x.round() == x
    }
    pub fn isInteger32(x: f64) -> bool {
        isInteger(x) &&
            (x.approx_as::<u32>().is_ok() || x.approx_as::<i32>().is_ok())
    }
    pub fn isInteger64(x: f64) -> bool {
        isInteger(x) &&
            (x.approx_as::<u64>().is_ok() || x.approx_as::<i64>().is_ok())
    }
    pub fn f64toi32(x: f64) -> i32 {
        assert!(isInteger(x));
        x.approx().unwrap()
    }
    pub fn f64toi64(x: f64) -> i64 {
        assert!(isInteger(x));
        x.approx().unwrap()
    }
    pub fn f64tou32(x: f64) -> u32 {
        assert!(isInteger(x));
        x.approx().unwrap()
    }
    pub fn f64tou64(x: f64) -> u64 {
        assert!(isInteger(x));
        x.approx().unwrap()
    }
    pub fn jsD2I(x: f64) -> i32 {
        assert!(isInteger(x));
        f64toi64(x) as i32
    }
}

use cashew::{AstValue, printAst};

// RSTODO: the asmfloatzero static is a pain, and needs to be
// defined in main and then given to all passes to use. What
// does it actually do?

// RSTODO: make these not global static
static mut preciseF32: bool = false;
static mut receiveJSON: bool = false;
static mut emitJSON: bool = false;
static mut minifyWhitespace: bool = false;
static mut last: bool = false;

pub fn libmain() {
    assert!(mem::size_of::<AstValue>() == 32);

    let args: Vec<String> = env::args().collect();
    // Read directives
    for arg in &args[2..] {
        unsafe {
            if arg == "asm" {} // the only possibility for us
            else if arg == "asmPreciseF32" { preciseF32 = true; }
            else if arg == "receiveJSON" { receiveJSON = true; }
            else if arg == "emitJSON" { emitJSON = true; }
            else if arg == "minifyWhitespace" { minifyWhitespace = true; }
            else if arg == "last" { last = true; }
        }
    }

    #[cfg(feature = "profiling")]
    let (profstg, profstart) = {
        let profstg = "reading and parsing";
        printlnerr!("starting {}", profstg);
        (profstg, time::SystemTime::now())
    };

    let mut input = {
        let mut f = fs::File::open(&args[1]).unwrap();
        let mut buf = String::new();
        f.read_to_string(&mut buf).unwrap();
        buf
    };

    let extraInfo = if let Some(extra_info_start) = input.find("// EXTRA_INFO:") {
        let json: serde_json::Value = serde_json::from_slice(&input.as_bytes()[extra_info_start+14..]).unwrap();
        input.truncate(extra_info_start); // ignore extra info when parsing
        json
    } else {
        serde_json::Value::Null
    };

    let mut doc = if unsafe { receiveJSON } {
        // Parse JSON source into the document
        AstValue::parse_json(input.as_bytes())
    } else {
        let mut builder = parser::Parser::new();
        input.push('\0');
        unsafe { builder.parseToplevel(input.as_ptr()) }
    };

    drop(input);

    #[cfg(feature = "profiling")]
    {
        let t = profstart.elapsed().unwrap();
        printlnerr!("    {} took {} milliseconds", profstg, t.to_ms());
    }

    // Run passes on the Document
    for arg in &args[2..] {
        #[cfg(feature = "profiling")]
        let (profstg, profstart) = {
            let profstg = arg;
            printlnerr!("starting {}", profstg);
            (profstg, time::SystemTime::now())
        };
        let mut worked = true;
        let doc = &mut *doc;
        match arg.as_str() {
            "asm" |
            "asmPreciseF32" |
            "minifyWhitespace" |
            "last" |
            "noop" |
            "emitJSON" |
            "receiveJSON" => worked = false,
            "eliminateDeadFuncs" => eliminateDeadFuncs(doc, &extraInfo),
            "eliminate" => eliminate(doc, false),
            "eliminateMemSafe" => eliminate(doc, true),
            "simplifyExpressions" => simplifyExpressions(doc, unsafe { preciseF32 }),
            "optimizeFrounds" => optimizeFrounds(doc),
            "simplifyIfs" => simplifyIfs(doc),
            "registerize" => registerize(doc),
            "registerizeHarder" => registerizeHarder(doc),
            "minifyLocals" => minifyLocals(doc, &extraInfo),
            "asmLastOpts" => asmLastOpts(doc),
            _ => {
                printlnerr!("Unrecognised argument: {}", arg);
                panic!()
            },
        }

        #[cfg(feature = "profiling")]
        {
            let t = profstart.elapsed().unwrap();
            printlnerr!("    {} took {} milliseconds", profstg, t.to_ms());
        }

        if DEBUG && worked {
            printlnerr!("ast after {}", arg);
            doc.stringify(&mut io::stderr(), false);
            printlnerr!("");
        }
    }

    // RSTODO: add profiling of emit to emoptimizer
    #[cfg(feature = "profiling")]
    let (profstg, profstart) = {
        let profstg = "final emit";
        printlnerr!("starting {}", profstg);
        (profstg, time::SystemTime::now())
    };
    // Emit
    if unsafe { emitJSON } {
        doc.stringify(&mut io::stdout(), false);
        println!("");
    } else {
        let ret = printAst(!unsafe { minifyWhitespace }, unsafe { last }, &doc);
        io::stdout().write_all(&ret).unwrap();
        println!("");
    }
    #[cfg(feature = "profiling")]
    {
        let t = profstart.elapsed().unwrap();
        printlnerr!("    {} took {} milliseconds", profstg, t.to_ms());
    }
}
