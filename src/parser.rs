// Pure parsing. Calls methods on a Builder (template argument) to actually
// construct the AST
//
// XXX All parsing methods assume they take ownership of the input string. This
// lets them reuse parts of it. You will segfault if the input string cannot be
// reused and written to.

use std::ptr;
use std::slice;
use std::str;
use std::{i32, u32};

use libc;
use libc::{c_char, c_int};

use phf;
use phf_builder;

use super::IString;
use super::cashew::builder;
use super::cashew::Ref;

lazy_static! {
    static ref KEYWORDS: phf::Set<IString> = iss![
        "var",
        "const",
        "function",
        "if",
        "else",
        "do",
        "while",
        "for",
        "break",
        "continue",
        "return",
        "switch",
        "case",
        "default",
        "throw",
        "try",
        "catch",
        "finally",
        "true",
        "false",
        "null",
        "new",
    ];

    static ref OP_CLASSES: Vec<OpClass> = vec![
        OpClass::new(iss!["."],               false, OpClassTy::Binary),
        OpClass::new(iss!["!","~","+","-"],   true,  OpClassTy::Prefix),
        OpClass::new(iss!["*","/","%"],       false, OpClassTy::Binary),
        OpClass::new(iss!["+","-"],           false, OpClassTy::Binary),
        OpClass::new(iss!["<<",">>",">>>"],   false, OpClassTy::Binary),
        OpClass::new(iss!["<","<=",">",">="], false, OpClassTy::Binary),
        OpClass::new(iss!["==","!="],         false, OpClassTy::Binary),
        OpClass::new(iss!["&"],               false, OpClassTy::Binary),
        OpClass::new(iss!["^"],               false, OpClassTy::Binary),
        OpClass::new(iss!["|"],               false, OpClassTy::Binary),
        OpClass::new(iss!["?",":"],           true,  OpClassTy::Tertiary),
        OpClass::new(iss!["="],               true,  OpClassTy::Binary),
        OpClass::new(iss![","],               true,  OpClassTy::Binary),
    ];

    static ref PRECEDENCES: Vec<phf::Map<IString, usize>> = {
        let mut prec_builders: Vec<_> = (0..OpClassTy::Tertiary as usize+1).map(|_|
            phf_builder::Map::new()
        ).collect();
        for (prec, oc) in OP_CLASSES.iter().enumerate() {
            for curr in &oc.ops {
                prec_builders[oc.ty as usize].entry(curr.clone(), prec);
            }
        }
        prec_builders.into_iter().map(|builder| builder.build()).collect()
    };
}

// Used in hasChar, must be a cstring
const OPERATOR_INITS: &'static [u8] = b"+-*/%<>&^|~=!,?:.\0";
const SEPARATORS: &'static [u8] = b"([;{}\0";

#[derive(Copy, Clone)]
enum OpClassTy {
    Binary = 0,
    Prefix = 1,
    Postfix = 2,
    Tertiary = 3,
}
struct OpClass {
    ops: phf::Set<IString>,
    rtl: bool,
    ty: OpClassTy,
}

impl OpClass {
    fn new(ops: phf::Set<IString>, rtl: bool, ty: OpClassTy) -> OpClass {
        OpClass { ops: ops, rtl: rtl, ty: ty }
    }

    fn getPrecedence(ty: OpClassTy, op: IString) -> usize {
        *PRECEDENCES[ty as usize].get(&op).unwrap()
    }

    fn getRtl(prec: usize) -> bool {
        OP_CLASSES[prec].rtl
    }
}

macro_rules! pp {
    { $p:ident += $off:expr } => {{ *$p = (*$p).offset($off) }};
    { $p:ident + $off:expr } => {{ (*$p).offset($off) }};
    { $p:ident[$off:expr] } => {{ *(*$p).offset($off) }};
}
macro_rules! p {
    { $p:ident += $off:expr } => {{ $p = $p.offset($off) }};
    { $p:ident + $off:expr } => {{ $p.offset($off) }};
    { $p:ident[$off:expr] } => {{ *$p.offset($off) }};
}

fn isIdentInit(x: u8) -> bool {
    (x >= b'a' && x <= b'z') || (x >= b'A' && x <= b'Z') || x == b'_' || x == b'$'
}
// RSTODO: use isDigit?
fn isIdentPart(x: u8) -> bool {
    isIdentInit(x) || (x >= b'0' && x <= b'9')
}
fn isSpace(x: u8) -> bool {
    // space, tab, linefeed/newline or return
    x == 32 || x == 9 || x == 10 || x == 13
}
fn isDigit(x: u8) -> bool {
    x >= b'0' && x <= b'9'
}
// RSTODO: this is an absolute disgrace
// https://github.com/rust-lang/rfcs/pull/1218
// https://doc.rust-lang.org/book/casting-between-types.html#numeric-casts (note UB)
// use https://crates.io/crates/conv ?
fn is32Bit(x: f64) -> bool {
    assert!(x.is_normal() || x == 0f64);
    if x > u32::MAX as f64 || x < i32::MIN as f64 { return false }
    if x.is_sign_positive() { return x as u32 as f64 == x }
    return x as i32 as f64 == x
}
fn f64tou32(x: f64) -> u32 {
    assert!(is32Bit(x) && x >= 0f64);
    x as u32
}
unsafe fn hasChar(list: *const u8, x: u8) -> bool {
    while p!{list[0]} != b'\0' {
        if p!{list[0]} == x {
            return true
        }
    }
    false
}

enum FragData {
    Keyword(IString),
    Operator(IString),
    Ident(IString),
    String(IString),
    Int(f64),
    Double(f64),
    Separator(IString),
}

// https://github.com/rust-lang/rust/issues/32836
// An atomic fragment of something. Stops at a natural boundary.
struct Frag {
    data: FragData,
    size: usize,
}

impl Frag {
    fn isNumber(&self) -> bool {
        match self.data {
            FragData::Int(_) | FragData::Double(_) => true,
            _ => false,
        }
    }

    fn getStr(&self) -> IString {
        match self.data {
            FragData::Keyword(ref s) |
            FragData::Operator(ref s) |
            FragData::Ident(ref s) |
            FragData::String(ref s) |
            FragData::Separator(ref s) => s.clone(),
            FragData::Int(_) |
            FragData::Double(_) => panic!(),
        }
    }

    fn parse(&self) -> Ref {
        match self.data {
            FragData::Ident(ref s) =>  builder::makeName(s.clone()),
            FragData::String(ref s) => builder::makeString(s.clone()),
            FragData::Int(f) =>    builder::makeInt(f64tou32(f)),
            FragData::Double(f) => builder::makeDouble(f),
            _ => panic!(),
        }
    }

    unsafe fn from_str(mut src: *const u8) -> Frag {
        let start = src;
        let fragdata = if isIdentInit(p!{src[0]}) {
            // read an identifier or a keyword
            p!{src+=1};
            while isIdentPart(*src) {
                p!{src+=1};
            }
            let b = slice::from_raw_parts(start, src as usize - start as usize);
            let s = str::from_utf8_unchecked(b);
            let is = IString::from(s);
            if KEYWORDS.contains(&is) {
                FragData::Keyword(is)
            } else {
                FragData::Ident(is)
            }
        } else if isDigit(p!{src[0]}) ||
                (p!{src[0]} == b'.' && isDigit(p!{src[1]})) {
            let num = if p!{src[0]} == b'0' &&
                    (p!{src[1]} == b'x' || p!{src[1]} == b'X') {
                // Explicitly parse hex numbers of form "0x...", because strtod
                // supports hex number strings only in C++11, and Visual Studio 2013
                // does not yet support that functionality.
                p!{src+=2};
                let mut num = 0;
                loop {
                    if p!{src[0]} >= b'0' && p!{src[0]} <= b'9' {
                        num *= 16; num += p!{src[0]} - b'0';
                    } else if p!{src[0]} >= b'a' && p!{src[0]} <= b'f' {
                        num *= 16; num += p!{src[0]} - b'a' + 10;
                    } else if p!{src[0]} >= b'A' && p!{src[0]} <= b'F' {
                        num *= 16; num += p!{src[0]} - b'F' + 10;
                    } else {
                        break
                    }
                    p!{src+=1};
                }
                num as f64
            } else {
                let mut ptr = ptr::null_mut();
                let num = libc::strtod(start as *const c_char, &mut ptr as *mut _);
                src = ptr as *const _;
                num
            };
            // asm.js must have a '.' for double values. however, we also tolerate
            // uglify's tendency to emit without a '.' (and fix it later with a +).
            // for valid asm.js input, the '.' should be enough, and for uglify
            // in the emscripten optimizer pipeline, we use simple_ast where
            // INT/DOUBLE is quite the same at this point anyhow
            let b = slice::from_raw_parts(start, src as usize - start as usize);
            if !b.contains(&b'.') && is32Bit(num) {
                FragData::Int(num)
            } else {
                FragData::Double(num)
            }
        } else if hasChar(OPERATOR_INITS.as_ptr(), p!{src[0]}) {
            let is = match p!{src[0]} {
                b'!' => if p!{src[1]} == b'=' { is!("!=") } else { is!("!") },
                b'%' => is!("%"),
                b'&' => is!("&"),
                b'*' => is!("*"),
                b'+' => is!("+"),
                b',' => is!(","),
                b'-' => is!("-"),
                b'.' => is!("."),
                b'/' => is!("/"),
                b':' => is!(":"),
                b'<' => match p!{src[1]} {
                            b'<' => is!("<<"),
                            b'=' => is!("<="),
                            _ => is!("<"),
                        },
                b'=' => if p!{src[1]} == b'=' { is!("==") } else { is!("=") },
                b'>' => match p!{src[1]} {
                            b'>' => if p!{src[2]} == b'>' { is!(">>>") } else { is!(">>") },
                            b'=' => is!(">="),
                            _ => is!(">"),
                        },
                b'?' => is!("?"),
                b'^' => is!("^"),
                b'|' => is!("|"),
                b'~' => is!("~"),
                _ => unreachable!(),
            };
            debug_assert!({
                let b = is.as_bytes();
                b == slice::from_raw_parts(start, b.len())
            });
            p!{src+=is.len() as isize};
            FragData::Operator(is)
        } else if hasChar(SEPARATORS.as_ptr(), p!{src[0]}) {
            let b = slice::from_raw_parts(src, 1);
            let s = str::from_utf8_unchecked(b);
            let is = IString::from(s);
            p!{src+=1};
            FragData::Separator(is)
        } else if p!{src[0]} == b'"' || p!{src[0]} == b'\'' {
            src = libc::strchr(p!{src+1} as *const c_char, p!{src[0]} as c_int)
                as *const _;
            p!{src+=1};
            let b = slice::from_raw_parts(src, src as usize - start as usize);
            let s = str::from_utf8_unchecked(b);
            let is = IString::from(s);
            FragData::String(is)
        } else {
            // RSTODO
            //Parser::dump("frag parsing".as_ptr(), src);
            panic!()
        };
        Frag {
            data: fragdata,
            size: src as usize - start as usize,
        }
    }
}

enum ExprElt {
    Node(Ref),
    Op(IString),
}

// RSTODO: may not be needed?
//  ExprElt(NodeRef n) : isNode(true), node(n) {}
//  ExprElt(IString o) : isNode(false), op(o) {}
//
//  NodeRef getNode() {
//    assert(isNode);
//    return node;
//  }
//  IString getOp() {
//    assert(!isNode);
//    return op;
//  }

// parser

struct Parser {
    // This is a list of the current stack of node-operator-node-operator-etc.
    // this works by each parseExpression call appending to the vector; then
    // recursing out, and the toplevel sorts it all
    expressionPartsStack: Vec<Vec<ExprElt>>,

    allSource: *const u8,
    allSize: usize,
}

unsafe fn skipSpace(curr: &mut *const u8) {
    while pp!{curr[0]} != b'\0' {
        if isSpace(pp!{curr[0]}) {
            pp!{curr+=1};
            continue
        }
        if pp!{curr[0]} == b'/' && pp!{curr[1]} == b'/' {
            pp!{curr+=2};
            while pp!{curr[0]} != b'\0' && pp!{curr[0]} != b'\n' {
                pp!{curr+=1};
            }
            if pp!{curr[0]} != b'\0' {
                pp!{curr+=1};
            }
            continue
        }
        if pp!{curr[0]} == b'/' && pp!{curr[1]} == b'*' {
            pp!{curr+=2};
            while pp!{curr[0]} != b'\0' &&
                    (pp!{curr[0]} != b'*' || pp!{curr[1]} != b'/') {
                pp!{curr+=1};
            }
            pp!{curr+=2};
            continue
        }
        return
    }
}

impl Parser {
    // Parses an element in a list of such elements, e.g. list of statements in a block, or list of parameters in a call
    unsafe fn parseElement(&mut self, src: &mut *const u8, seps: *const u8) -> Ref {
        //dump("parseElement", src);
        skipSpace(src);
        let frag = Frag::from_str(*src);
        pp!{src+=frag.size as isize};
        match frag.data {
            FragData::Keyword(_) => self.parseAfterKeyword(&frag, src, seps),
            FragData::Ident(_) => self.parseAfterIdent(&frag, src, seps),
            FragData::String(_) |
            FragData::Int(_) |
            FragData::Double(_) => self.parseExpression(ExprElt::Node(frag.parse()), src, seps),
            FragData::Separator(s) => {
                let eenode = match s {
                    is!("(") => self.parseAfterParen(src),
                    is!("[") => self.parseAfterBrace(src),
                    is!("{") => self.parseAfterCurly(src),
                    _ => panic!(),
                };
                self.parseExpression(ExprElt::Node(eenode), src, seps)
            },
            FragData::Operator(s) => self.parseExpression(ExprElt::Op(s), src, seps),
        }
    }

    unsafe fn parseAfterKeyword(&mut self, frag: &Frag, src: &mut *const u8, seps: *const u8) -> Ref {
        skipSpace(src);
        match frag.getStr() {
            is!("function") => self.parseFunction(src, seps),
            is!("var") |
            is!("const") => self.parseVar(src, seps, false),
            is!("return") => self.parseReturn(src, seps),
            is!("if") => self.parseIf(src, seps),
            is!("do") => self.parseDo(src, seps),
            is!("while") => self.parseWhile(src, seps),
            is!("break") => self.parseBreak(src, seps),
            is!("continue") => self.parseContinue(src, seps),
            is!("switch") => self.parseSwitch(src, seps),
            is!("new") => self.parseNew(src, seps),
            _ => panic!(),
        }
    }

    // RSTODO: remove seps?
    unsafe fn parseFunction(&mut self, src: &mut *const u8, _seps: *const u8) -> Ref {
        let name_str = match Frag::from_str(*src) {
            Frag { data: FragData::Ident(s), size: n } => { pp!{src+=n as isize}; s },
            Frag { data: FragData::Separator(is!("(")), .. } => is!(""),
            _ => panic!(),
        };
        let ret = builder::makeFunction(name_str);
        skipSpace(src);
        assert!(pp!{src[0]} == b'(');
        pp!{src+=1};
        loop {
            skipSpace(src);
            if pp!{src[0]} == b')' { break }
            if let Frag { data: FragData::Ident(s), size: n } = Frag::from_str(*src) {
                pp!{src+=n as isize};
                builder::appendArgumentToFunction(ret, s)
            } else {
                panic!()
            }
            skipSpace(src);
            match pp!{src[0]} {
                b')' => break,
                b',' => { pp!{src+=1}; continue },
                _ => panic!(),
            }
        }
        pp!{src+=1};
        builder::setBlockContent(ret, self.parseBracketedBlock(src));
        // TODO: parse expression?
        ret
    }

    // RSTODO: remove seps?
    unsafe fn parseVar(&mut self, src: &mut *const u8, _seps: *const u8, is_const: bool) -> Ref {
        let ret = builder::makeVar(is_const);
        loop {
            skipSpace(src);
            if pp!{src[0]} == b';' { break }
            let name_str = if let Frag { data: FragData::Ident(s), size: n } = Frag::from_str(*src) {
                pp!{src+=n as isize};
                s
            } else {
                panic!()
            };
            skipSpace(src);
            let value = if pp!{src[0]} == b'=' {
                pp!{src+=1};
                skipSpace(src);
                Some(self.parseElement(src, b";,\0".as_ptr()))
            } else {
                None
            };
            builder::appendToVar(ret, name_str, value);
            skipSpace(src);
            match pp!{src[0]} {
                b';' => break,
                b',' => { pp!{src+=1}; continue },
                _ => panic!(),
            }
        }
        pp!{src+=1};
        ret
    }

    // RSTODO
    unsafe fn parseReturn(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseReturn(char*& src, const char* seps) {
//    skipSpace(src);
//    NodeRef value = !hasChar(seps, *src) ? parseElement(src, seps) : nullptr;
//    skipSpace(src);
//    assert(hasChar(seps, *src));
//    if (*src == ';') src++;
//    return Builder::makeReturn(value);
//  }

    // RSTODO
    unsafe fn parseIf(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseIf(char*& src, const char* seps) {
//    NodeRef condition = parseParenned(src);
//    NodeRef ifTrue = parseMaybeBracketed(src, seps);
//    skipSpace(src);
//    NodeRef ifFalse;
//    if (!hasChar(seps, *src)) {
//      Frag next(src);
//      if (next.type == KEYWORD && next.str == ELSE) {
//        src += next.size;
//        ifFalse = parseMaybeBracketed(src, seps);
//      }
//    }
//    return Builder::makeIf(condition, ifTrue, ifFalse);
//  }

    // RSTODO
    unsafe fn parseDo(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseDo(char*& src, const char* seps) {
//    NodeRef body = parseMaybeBracketed(src, seps);
//    skipSpace(src);
//    Frag next(src);
//    assert(next.type == KEYWORD && next.str == WHILE);
//    src += next.size;
//    NodeRef condition = parseParenned(src);
//    return Builder::makeDo(body, condition);
//  }

    // RSTODO
    unsafe fn parseWhile(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseWhile(char*& src, const char* seps) {
//    NodeRef condition = parseParenned(src);
//    NodeRef body = parseMaybeBracketed(src, seps);
//    return Builder::makeWhile(condition, body);
//  }

    // RSTODO
    unsafe fn parseBreak(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseBreak(char*& src, const char* seps) {
//    skipSpace(src);
//    Frag next(src);
//    if (next.type == IDENT) src += next.size;
//    return Builder::makeBreak(next.type == IDENT ? next.str : IString());
//  }

    // RSTODO
    unsafe fn parseContinue(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseContinue(char*& src, const char* seps) {
//    skipSpace(src);
//    Frag next(src);
//    if (next.type == IDENT) src += next.size;
//    return Builder::makeContinue(next.type == IDENT ? next.str : IString());
//  }

    // RSTODO
    unsafe fn parseSwitch(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseSwitch(char*& src, const char* seps) {
//    NodeRef ret = Builder::makeSwitch(parseParenned(src));
//    skipSpace(src);
//    assert(*src == '{');
//    src++;
//    while (1) {
//      // find all cases and possibly a default
//      skipSpace(src);
//      if (*src == '}') break;
//      Frag next(src);
//      if (next.type == KEYWORD) {
//        if (next.str == CASE) {
//          src += next.size;
//          skipSpace(src);
//          NodeRef arg;
//          Frag value(src);
//          if (value.isNumber()) {
//            arg = parseFrag(value);
//            src += value.size;
//          } else {
//            assert(value.type == OPERATOR);
//            assert(value.str == MINUS);
//            src += value.size;
//            skipSpace(src);
//            Frag value2(src);
//            assert(value2.isNumber());
//            arg = Builder::makePrefix(MINUS, parseFrag(value2));
//            src += value2.size;
//          }
//          Builder::appendCaseToSwitch(ret, arg);
//          skipSpace(src);
//          assert(*src == ':');
//          src++;
//          continue;
//        } else if (next.str == DEFAULT) {
//          src += next.size;
//          Builder::appendDefaultToSwitch(ret);
//          skipSpace(src);
//          assert(*src == ':');
//          src++;
//          continue;
//        }
//        // otherwise, may be some keyword that happens to start a block (e.g. case 1: _return_ 5)
//      }
//      // not case X: or default: or }, so must be some code
//      skipSpace(src);
//      bool explicitBlock = *src == '{';
//      NodeRef subBlock = explicitBlock ? parseBracketedBlock(src) : parseBlock(src, ";}", CASE, DEFAULT);
//      Builder::appendCodeToSwitch(ret, subBlock, explicitBlock);
//    }
//    skipSpace(src);
//    assert(*src == '}');
//    src++;
//    return ret;
//  }

    // RSTODO
    unsafe fn parseNew(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseNew(char*& src, const char* seps) {
//    return Builder::makeNew(parseElement(src, seps));
//  }

    // RSTODO
    unsafe fn parseAfterIdent(&mut self, _frag: &Frag, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseAfterIdent(Frag& frag, char*& src, const char* seps) {
//    skipSpace(src);
//    if (*src == '(') return parseExpression(parseCall(parseFrag(frag), src), src, seps);
//    if (*src == '[') return parseExpression(parseIndexing(parseFrag(frag), src), src, seps);
//    if (*src == ':' && expressionPartsStack.back().size() == 0) {
//      src++;
//      skipSpace(src);
//      NodeRef inner;
//      if (*src == '{') { // context lets us know this is not an object, but a block
//        inner = parseBracketedBlock(src);
//      } else {
//        inner = parseElement(src, seps);
//      }
//      return Builder::makeLabel(frag.str, inner);
//    }
//    if (*src == '.') return parseExpression(parseDotting(parseFrag(frag), src), src, seps);
//    return parseExpression(parseFrag(frag), src, seps);
//  }

    // RSTODO
    unsafe fn parseCall(&mut self, _target: Ref, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseCall(NodeRef target, char*& src) {
//    expressionPartsStack.resize(expressionPartsStack.size()+1);
//    assert(*src == '(');
//    src++;
//    NodeRef ret = Builder::makeCall(target);
//    while (1) {
//      skipSpace(src);
//      if (*src == ')') break;
//      Builder::appendToCall(ret, parseElement(src, ",)"));
//      skipSpace(src);
//      if (*src == ')') break;
//      if (*src == ',') {
//        src++;
//        continue;
//      }
//      abort();
//    }
//    src++;
//    assert(expressionPartsStack.back().size() == 0);
//    expressionPartsStack.pop_back();
//    return ret;
//  }

    // RSTODO
    unsafe fn parseIndexing(&mut self, _target: Ref, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseIndexing(NodeRef target, char*& src) {
//    expressionPartsStack.resize(expressionPartsStack.size()+1);
//    assert(*src == '[');
//    src++;
//    NodeRef ret = Builder::makeIndexing(target, parseElement(src, "]"));
//    skipSpace(src);
//    assert(*src == ']');
//    src++;
//    assert(expressionPartsStack.back().size() == 0);
//    expressionPartsStack.pop_back();
//    return ret;
//  }

    // RSTODO
    unsafe fn parseDotting(&mut self, _target: Ref, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseDotting(NodeRef target, char*& src) {
//    assert(*src == '.');
//    src++;
//    Frag key(src);
//    assert(key.type == IDENT);
//    src += key.size;
//    return Builder::makeDot(target, key.str);
//  }

    // RSTODO
    unsafe fn parseAfterParen(&mut self, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseAfterParen(char*& src) {
//    expressionPartsStack.resize(expressionPartsStack.size()+1);
//    skipSpace(src);
//    NodeRef ret = parseElement(src, ")");
//    skipSpace(src);
//    assert(*src == ')');
//    src++;
//    assert(expressionPartsStack.back().size() == 0);
//    expressionPartsStack.pop_back();
//    return ret;
//  }

    // RSTODO
    unsafe fn parseAfterBrace(&mut self, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseAfterBrace(char*& src) {
//    expressionPartsStack.resize(expressionPartsStack.size()+1);
//    NodeRef ret = Builder::makeArray();
//    while (1) {
//      skipSpace(src);
//      assert(*src);
//      if (*src == ']') break;
//      NodeRef element = parseElement(src, ",]");
//      Builder::appendToArray(ret, element);
//      skipSpace(src);
//      if (*src == ']') break;
//      if (*src == ',') {
//        src++;
//        continue;
//      }
//      abort();
//    }
//    src++;
//    return ret;
//  }

    // RSTODO
    unsafe fn parseAfterCurly(&mut self, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseAfterCurly(char*& src) {
//    expressionPartsStack.resize(expressionPartsStack.size()+1);
//    NodeRef ret = Builder::makeObject();
//    while (1) {
//      skipSpace(src);
//      assert(*src);
//      if (*src == '}') break;
//      Frag key(src);
//      assert(key.type == IDENT || key.type == STRING);
//      src += key.size;
//      skipSpace(src);
//      assert(*src == ':');
//      src++;
//      NodeRef value = parseElement(src, ",}");
//      Builder::appendToObject(ret, key.str, value);
//      skipSpace(src);
//      if (*src == '}') break;
//      if (*src == ',') {
//        src++;
//        continue;
//      }
//      abort();
//    }
//    src++;
//    return ret;
//  }

    // RSTODO
    unsafe fn makeBinary(_left: Ref, _op: IString, _right: Ref) -> Ref {
        panic!()
    }
//  NodeRef makeBinary(NodeRef left, IString op, NodeRef right) {
//    if (op == PERIOD) {
//      return Builder::makeDot(left, right);
//    } else {
//      return Builder::makeBinary(left, op ,right);
//    }
//  }

    // RSTODO
    unsafe fn parseExpression(&mut self, _initial: ExprElt, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseExpression(ExprElt initial, char*&src, const char* seps) {
//    //dump("parseExpression", src);
//    ExpressionParts& parts = expressionPartsStack.back();
//    skipSpace(src);
//    if (*src == 0 || hasChar(seps, *src)) {
//      if (parts.size() > 0) {
//        parts.push_back(initial); // cherry on top of the cake
//      }
//      return initial.getNode();
//    }
//    bool top = parts.size() == 0;
//    if (initial.isNode) {
//      Frag next(src);
//      if (next.type == OPERATOR) {
//        parts.push_back(initial);
//        src += next.size;
//        parts.push_back(next.str);
//      } else {
//        if (*src == '(') {
//          initial = parseCall(initial.getNode(), src);
//        } else if (*src == '[') {
//          initial = parseIndexing(initial.getNode(), src);
//        } else {
//          dump("bad parseExpression state", src);
//          abort();
//        }
//        return parseExpression(initial, src, seps);
//      }
//    } else {
//      parts.push_back(initial);
//    }
//    NodeRef last = parseElement(src, seps);
//    if (!top) return last;
//    {
//      ExpressionParts& parts = expressionPartsStack.back(); // |parts| may have been invalidated by that call
//      // we are the toplevel. sort it all out
//      // collapse right to left, highest priority first
//      //dumpParts(parts, 0);
//      for (auto& ops : operatorClasses) {
//        if (ops.rtl) {
//          // right to left
//          for (int i = parts.size()-1; i >= 0; i--) {
//            if (parts[i].isNode) continue;
//            IString op = parts[i].getOp();
//            if (!ops.ops.has(op)) continue;
//            if (ops.type == OperatorClass::Binary && i > 0 && i < (int)parts.size()-1) {
//              parts[i] = makeBinary(parts[i-1].getNode(), op, parts[i+1].getNode());
//              parts.erase(parts.begin() + i + 1);
//              parts.erase(parts.begin() + i - 1);
//            } else if (ops.type == OperatorClass::Prefix && i < (int)parts.size()-1) {
//              if (i > 0 && parts[i-1].isNode) continue; // cannot apply prefix operator if it would join two nodes
//              parts[i] = Builder::makePrefix(op, parts[i+1].getNode());
//              parts.erase(parts.begin() + i + 1);
//            } else if (ops.type == OperatorClass::Tertiary) {
//              // we must be at  X ? Y : Z
//              //                      ^
//              //dumpParts(parts, i);
//              if (op != COLON) continue;
//              assert(i < (int)parts.size()-1 && i >= 3);
//              if (parts[i-2].getOp() != QUESTION) continue; // e.g. x ? y ? 1 : 0 : 2
//              parts[i-3] = Builder::makeConditional(parts[i-3].getNode(), parts[i-1].getNode(), parts[i+1].getNode());
//              parts.erase(parts.begin() + i - 2, parts.begin() + i + 2);
//              i = parts.size(); // basically a reset, due to things like x ? y ? 1 : 0 : 2
//            } // TODO: postfix
//          }
//        } else {
//          // left to right
//          for (int i = 0; i < (int)parts.size(); i++) {
//            if (parts[i].isNode) continue;
//            IString op = parts[i].getOp();
//            if (!ops.ops.has(op)) continue;
//            if (ops.type == OperatorClass::Binary && i > 0 && i < (int)parts.size()-1) {
//              parts[i] = makeBinary(parts[i-1].getNode(), op, parts[i+1].getNode());
//              parts.erase(parts.begin() + i + 1);
//              parts.erase(parts.begin() + i - 1);
//              i--;
//            } else if (ops.type == OperatorClass::Prefix && i < (int)parts.size()-1) {
//              if (i > 0 && parts[i-1].isNode) continue; // cannot apply prefix operator if it would join two nodes
//              parts[i] = Builder::makePrefix(op, parts[i+1].getNode());
//              parts.erase(parts.begin() + i + 1);
//              i = std::max(i-2, 0); // allow a previous prefix operator to cascade
//            } // TODO: tertiary, postfix
//          }
//        }
//      }
//      assert(parts.size() == 1);
//      NodeRef ret = parts[0].getNode();
//      parts.clear();
//      return ret;
//    }
//  }

    // RSTODO
    unsafe fn parseBlock(&mut self, _src: &mut *const u8, _seps: *const u8, _keywordSep1: Option<IString>, _keywordSep2: Option<IString>) -> Ref {
        panic!()
    }
//  // Parses a block of code (e.g. a bunch of statements inside {,}, or the top level of o file)
//  NodeRef parseBlock(char*& src, const char* seps=";", IString keywordSep1=IString(), IString keywordSep2=IString()) {
//    NodeRef block = Builder::makeBlock();
//    //dump("parseBlock", src);
//    while (1) {
//      skipSpace(src);
//      if (*src == 0) break;
//      if (*src == ';') {
//        src++; // skip a statement in this block
//        continue;
//      }
//      if (hasChar(seps, *src)) break;
//      if (!!keywordSep1) {
//        Frag next(src);
//        if (next.type == KEYWORD && next.str == keywordSep1) break;
//      }
//      if (!!keywordSep2) {
//        Frag next(src);
//        if (next.type == KEYWORD && next.str == keywordSep2) break;
//      }
//      NodeRef element = parseElementOrStatement(src, seps);
//      Builder::appendToBlock(block, element);
//    }
//    return block;
//  }

    // RSTODO
    unsafe fn parseBracketedBlock(&mut self, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseBracketedBlock(char*& src) {
//    skipSpace(src);
//    assert(*src == '{');
//    src++;
//    NodeRef block = parseBlock(src, ";}"); // the two are not symmetrical, ; is just internally separating, } is the final one - parseBlock knows all this
//    assert(*src == '}');
//    src++;
//    return block;
//  }

    // RSTODO
    unsafe fn parseElementOrStatement(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseElementOrStatement(char*& src, const char *seps) {
//    skipSpace(src);
//    if (*src == ';') {
//      src++;
//      return Builder::makeBlock(); // we don't need the brackets here, but oh well
//    }
//    if (*src == '{') { // detect a trivial {} in a statement context
//      char *before = src;
//      src++;
//      skipSpace(src);
//      if (*src == '}') {
//        src++;
//        return Builder::makeBlock(); // we don't need the brackets here, but oh well
//      }
//      src = before;
//    }
//    NodeRef ret = parseElement(src, seps);
//    skipSpace(src);
//    if (*src == ';') {
//      ret = Builder::makeStatement(ret);
//      src++;
//    }
//    return ret;
//  }

    // RSTODO
    unsafe fn parseMaybeBracketed(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseMaybeBracketed(char*& src, const char *seps) {
//    skipSpace(src);
//    return *src == '{' ? parseBracketedBlock(src) : parseElementOrStatement(src, seps);
//  }

    // RSTODO
    unsafe fn parseParenned(&mut self, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseParenned(char*& src) {
//    skipSpace(src);
//    assert(*src == '(');
//    src++;
//    NodeRef ret = parseElement(src, ")");
//    skipSpace(src);
//    assert(*src == ')');
//    src++;
//    return ret;
//  }

    fn new() -> Parser {
        Parser {
            expressionPartsStack: vec![vec![]],
            allSource: ptr::null(),
            allSize: 0,
        }
    }

    // RSTODO
    unsafe fn parseToplevel(&mut self, _src: &mut *const u8) -> Ref {
        panic!()
    }
//  // Highest-level parsing, as of a JavaScript script file.
//  NodeRef parseToplevel(char* src) {
//    allSource = src;
//    allSize = strlen(src);
//    NodeRef toplevel = Builder::makeToplevel();
//    Builder::setBlockContent(toplevel, parseBlock(src));
//    return toplevel;
//  }
//};

    // Debugging

    // RSTODO
    unsafe fn dump(&mut self, _msg: *const u8, _curr: *const u8) {
        panic!()
    }
//  static void dump(const char *where, char* curr) {
//    /*
//    printf("%s:\n=============\n", where);
//    for (int i = 0; i < allSize; i++) printf("%c", allSource[i] ? allSource[i] : '?');
//    printf("\n");
//    for (int i = 0; i < (curr - allSource); i++) printf(" ");
//    printf("^\n=============\n");
//    */
//    fprintf(stderr, "%s:\n==========\n", where);
//    int newlinesLeft = 2;
//    int charsLeft = 200;
//    while (*curr) {
//      if (*curr == '\n') {
//        newlinesLeft--;
//        if (newlinesLeft == 0) break;
//      }
//      charsLeft--;
//      if (charsLeft == 0) break;
//      fprintf(stderr, "%c", *curr++);
//    }
//    fprintf(stderr, "\n\n");
//  }

    // RSTODO
    unsafe fn dumpParts(_parts: Vec<Vec<ExprElt>>, _i: usize) {
        panic!()
    }
//  void dumpParts(ExpressionParts& parts, int i) {
//    printf("expressionparts: %d (at %d)\n", parts.size(), i);
//    printf("| ");
//    for (int i = 0; i < parts.size(); i++) {
//      if (parts[i].isNode) {
//        parts[i].getNode()->stringify(std::cout);
//        printf("    ");
//      } else {
//        printf("    _%s_    ", parts[i].getOp().str);
//      }
//    }
//    printf("|\n");
//  }
//

}

