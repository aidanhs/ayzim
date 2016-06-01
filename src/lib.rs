#![feature(stmt_expr_attributes, const_fn, box_patterns, slice_patterns)]
#![allow(non_snake_case, non_camel_case_types)]

// RSTODO: https://github.com/rust-lang/rust/issues/29599
#![feature(plugin)]
#![plugin(interpolate_idents)]
#![plugin(ayzim_macros)]

// RSTODO: review all numeric casts
// https://github.com/rust-lang/rfcs/pull/1218

// RSTODO: remove
#![allow(dead_code)]

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

use std::env;
use std::fs;
use std::io;
use std::io::{Read, Write};
use std::mem;
#[cfg(feature = "profiling")]
use std::time;

use optimizer::{
    //eliminateDeadFuncs
    //eliminate
    //eliminateMemSafe
    //simplifyExpressions
    //optimizeFrounds
    //simplifyIfs
    //registerize
    //registerizeHarder
    //minifyLocals
    //asmLastOpts
};

const DEBUG: bool = false;

include!(concat!(env!("OUT_DIR"), "/static_atoms.rs"));

// RSTODO: not sure why tt can't be expr in this macro?
macro_rules! iss {
    [ $( $x:tt ),+, ] => { iss![ $( $x ),+ ] };
    [ $( $x:tt ),* ] => {{
        let mut set = $crate::phf_builder::Set::new();
        $(
            set.entry(is!($x));
        )+
        set.build()
    }};
}

macro_rules! printlnerr(
    ($($arg:tt)*) => {{
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    }};
);

#[macro_use]
mod cashew;
mod optimizer;
mod parser;

mod num {
    use std::{i64, i32, u32};
    // RSTODO: this is an absolute disgrace
    // https://github.com/rust-lang/rfcs/pull/1218
    // https://doc.rust-lang.org/book/casting-between-types.html#numeric-casts (note UB)
    // use https://crates.io/crates/conv ?
    pub fn is32Bit(x: f64) -> bool {
        assert!(x.is_normal() || x == 0f64);
        if x > u32::MAX as f64 || x < i32::MIN as f64 { return false }
        if x.is_sign_positive() { return x as u32 as f64 == x }
        return x as i32 as f64 == x
    }
    pub fn f64tou32(x: f64) -> u32 {
        assert!(is32Bit(x) && x >= 0f64);
        x as u32
    }
    pub fn f64toi64(x: f64) -> i64 {
        assert!(isInteger(x));
        assert!(x <= i64::MAX as f64 && x >= i64::MIN as f64);
        x as i64
    }
    pub fn f64toi32(x: f64) -> i32 {
        assert!(is32Bit(x) && x <= i32::MAX as f64);
        x as i32
    }
    pub fn isInteger(x: f64) -> bool {
        assert!(x.is_normal() || x == 0f64);
        x.round() == x
    }
    pub fn isInteger32(x: f64) -> bool {
        is32Bit(x)
    }
}

use cashew::{ARENA, AstValue};

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

    let mut extraInfo = ARENA.alloc();
    if let Some(extra_info_start) = input.find("// EXTRA_INFO:") {
        extraInfo.parse(&input.as_bytes()[extra_info_start+14..]);
        input.truncate(extra_info_start); // ignore extra info when parsing
    }

    let doc = if unsafe { receiveJSON } {
        // Parse JSON source into the document
        let mut docref = ARENA.alloc();
        docref.parse(input.as_bytes());
        AstValue::from_ref(docref)
    } else {
        let mut builder = parser::Parser::new();
        input.push('\0');
        unsafe { builder.parseToplevel(input.as_ptr()) }
    };
    // RSTODO: pretty sure comment below is irrelevant
    // do not free input, its contents are used as strings

    #[cfg(feature = "profiling")]
    {
        let t = profstart.elapsed().unwrap();
        let t_ms = t.as_secs()*1000 + t.subsec_nanos() as u64/1_000_000;
        printlnerr!("    {} took {} milliseconds", profstg, t_ms);
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
        match arg.as_str() {
            "asm" => worked = false,
            "asmPreciseF32" => worked = false,
            "receiveJSON" |
            "emitJSON" => worked = false,
            //"eliminateDeadFuncs" => eliminateDeadFuncs(doc),
            //"eliminate" => eliminate(doc),
            //"eliminateMemSafe" => eliminateMemSafe(doc),
            //"simplifyExpressions" => simplifyExpressions(doc),
            //"optimizeFrounds" => optimizeFrounds(doc),
            //"simplifyIfs" => simplifyIfs(doc),
            //"registerize" => registerize(doc),
            //"registerizeHarder" => registerizeHarder(doc),
            //"minifyLocals" => minifyLocals(doc),
            "minifyWhitespace" => worked = false,
            //"asmLastOpts" => asmLastOpts(doc),
            "last" => worked = false,
            "noop" => worked = false,
            _ => {
                printlnerr!("Unrecognised argument: {}", arg);
                panic!()
            },
        }

        #[cfg(feature = "profiling")]
        {
            let t = profstart.elapsed().unwrap();
            let t_ms = t.as_secs()*1000 + t.subsec_nanos() as u64/1_000_000;
            printlnerr!("    {} took {} milliseconds", profstg, t_ms);
        }

        if DEBUG && worked {
            printlnerr!("ast after {}", arg);
            doc.stringify(&mut io::stderr(), false);
            printlnerr!("");
        }
    }

    // Emit
    if unsafe { emitJSON } {
        doc.stringify(&mut io::stdout(), false);
        println!("");
    } else {
        unimplemented!()
        // RSTODO
        //JSPrinter jser(!minifyWhitespace, last, doc);
        //jser.printAst();
        //std::cout << jser.buffer << "\n";
    }
}
