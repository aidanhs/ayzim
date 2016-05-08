#![feature(stmt_expr_attributes, const_fn)]
#![allow(non_snake_case, non_camel_case_types)]

// RSTODO: remove
#![allow(dead_code)]

#[macro_use]
extern crate lazy_static;
extern crate string_cache;
extern crate serde_json;
extern crate odds;
extern crate phf;
extern crate phf_builder;
extern crate smallvec;

use std::env;
use std::fs;
use std::io::Read;
#[cfg(profiling)]
use std::time;

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

mod cashew;
mod parser;

static mut preciseF32: bool = false;
static mut receiveJSON: bool = false;
static mut emitJSON: bool = false;
static mut minifyWhitespace: bool = false;
static mut last: bool = false;

pub fn libmain() {
    let args: Vec<String> = env::args().collect();
    for arg in &args[2..] {
        unsafe {
            if arg == "asm" {}
            else if arg == "asmPreciseF32" { preciseF32 = true; }
            else if arg == "receiveJSON" { receiveJSON = true; }
            else if arg == "emitJSON" { emitJSON = true; }
            else if arg == "minifyWhitespace" { minifyWhitespace = true; }
            else if arg == "last" { last = true; }
        }
    }
    #[cfg(profiling)]
    let start = {
        let profstg = "reading and parsing";
        println!("starting {}", profstg);
        time::SystemTime::now()
    };

    let mut input = {
        let mut f = fs::File::open(&args[1]).unwrap();
        let mut buf = String::new();
        f.read_to_string(&mut buf).unwrap();
        buf
    };

    if let Some(extra_info_start) = input.find("// EXTRA_INFO:") {
        // RSTODO
        //extraInfo = arena.alloc();
        //extraInfo->parse(extraInfoStart + 14);
        input.truncate(extra_info_start); // ignore extra info when parsing
    }
}
//  Ref doc;
//
//  if (receiveJSON) {
//    // Parse JSON source into the document
//    doc = arena.alloc();
//    doc->parse(input);
//  } else {
//    cashew::Parser<Ref, ValueBuilder> builder;
//    doc = builder.parseToplevel(input);
//  }
//  // do not free input, its contents are used as strings
//
//#ifdef PROFILING
//    errv("    %s took %lu milliseconds", str.c_str(), (clock() - start)/1000);
//#endif
//
//  // Run passes on the Document
//  for (int i = 2; i < argc; i++) {
//    std::string str(argv[i]);
//#ifdef PROFILING
//    clock_t start = clock();
//    errv("starting %s", str.c_str());
//#endif
//    bool worked = true;
//    if (str == "asm") { worked = false; } // the default for us
//    else if (str == "asmPreciseF32") { worked = false; }
//    else if (str == "receiveJSON" || str == "emitJSON") { worked = false; }
//    else if (str == "eliminateDeadFuncs") eliminateDeadFuncs(doc);
//    else if (str == "eliminate") eliminate(doc);
//    else if (str == "eliminateMemSafe") eliminateMemSafe(doc);
//    else if (str == "simplifyExpressions") simplifyExpressions(doc);
//    else if (str == "optimizeFrounds") optimizeFrounds(doc);
//    else if (str == "simplifyIfs") simplifyIfs(doc);
//    else if (str == "registerize") registerize(doc);
//    else if (str == "registerizeHarder") registerizeHarder(doc);
//    else if (str == "minifyLocals") minifyLocals(doc);
//    else if (str == "minifyWhitespace") { worked = false; }
//    else if (str == "asmLastOpts") asmLastOpts(doc);
//    else if (str == "last") { worked = false; }
//    else if (str == "noop") { worked = false; }
//    else {
//      fprintf(stderr, "unrecognized argument: %s\n", str.c_str());
//      abort();
//    }
//#ifdef PROFILING
//    errv("    %s took %lu milliseconds", str.c_str(), (clock() - start)/1000);
//#endif
//#ifdef DEBUGGING
//    if (worked) {
//      std::cerr << "ast after " << str << ":\n";
//      doc->stringify(std::cerr);
//      std::cerr << "\n";
//    }
//#endif
//  }
//
//  // Emit
//  if (emitJSON) {
//    doc->stringify(std::cout);
//    std::cout << "\n";
//  } else {
//    JSPrinter jser(!minifyWhitespace, last, doc);
//    jser.printAst();
//    std::cout << jser.buffer << "\n";
//  }
//  return 0;
//}
//
//}
