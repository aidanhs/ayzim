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

enum ExpressionElement {
    Node(Ref),
    Op(IString),
}

// RSTODO: may not be needed?
//  ExpressionElement(NodeRef n) : isNode(true), node(n) {}
//  ExpressionElement(IString o) : isNode(false), op(o) {}
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
    expressionPartsStack: Vec<Vec<ExpressionElement>>,

    allSource: *const u8,
    allSize: usize,
}

impl Parser {
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

    // Parses an element in a list of such elements, e.g. list of statements in a block, or list of parameters in a call
    // RSTODO
    fn parseElement(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseElement(char*& src, const char* seps=";") {
//    //dump("parseElement", src);
//    skipSpace(src);
//    Frag frag(src);
//    src += frag.size;
//    switch (frag.type) {
//      case KEYWORD: {
//        return parseAfterKeyword(frag, src, seps);
//      }
//      case IDENT: {
//        return parseAfterIdent(frag, src, seps);
//      }
//      case STRING:
//      case INT:
//      case DOUBLE: {
//        return parseExpression(parseFrag(frag), src, seps);
//      }
//      case SEPARATOR: {
//        if (frag.str == OPEN_PAREN) return parseExpression(parseAfterParen(src), src, seps);
//        if (frag.str == OPEN_BRACE) return parseExpression(parseAfterBrace(src), src, seps);
//        if (frag.str == OPEN_CURLY) return parseExpression(parseAfterCurly(src), src, seps);
//        abort();
//      }
//      case OPERATOR: {
//        return parseExpression(frag.str, src, seps);
//      }
//      default: /* dump("parseElement", src); printf("bad frag type: %d\n", frag.type); */ abort();
//    }
//    return nullptr;
//  }

    // RSTODO
    fn parseFrag(&mut self, _frag: &Frag) -> Ref {
        panic!()
    }
//  NodeRef parseFrag(Frag& frag) {
//    switch (frag.type) {
//      case IDENT:  return Builder::makeName(frag.str);
//      case STRING: return Builder::makeString(frag.str);
//      case INT:    return Builder::makeInt(uint32_t(frag.num));
//      case DOUBLE: return Builder::makeDouble(frag.num);
//      default: abort();
//    }
//    return nullptr;
//  }

    // RSTODO
    fn parseAfterKeyword(&mut self, _frag: &Frag, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseAfterKeyword(Frag& frag, char*& src, const char* seps) {
//    skipSpace(src);
//    if (frag.str == FUNCTION) return parseFunction(src, seps);
//    else if (frag.str == VAR) return parseVar(src, seps, false);
//    else if (frag.str == CONST) return parseVar(src, seps, true);
//    else if (frag.str == RETURN) return parseReturn(src, seps);
//    else if (frag.str == IF) return parseIf(src, seps);
//    else if (frag.str == DO) return parseDo(src, seps);
//    else if (frag.str == WHILE) return parseWhile(src, seps);
//    else if (frag.str == BREAK) return parseBreak(src, seps);
//    else if (frag.str == CONTINUE) return parseContinue(src, seps);
//    else if (frag.str == SWITCH) return parseSwitch(src, seps);
//    else if (frag.str == NEW) return parseNew(src, seps);
//    dump(frag.str.str, src);
//    abort();
//    return nullptr;
//  }

    // RSTODO
    fn parseFunction(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseFunction(char*& src, const char* seps) {
//    Frag name(src);
//    if (name.type == IDENT) {
//      src += name.size;
//    } else {
//      assert(name.type == SEPARATOR && name.str[0] == '(');
//      name.str = IString();
//    }
//    NodeRef ret = Builder::makeFunction(name.str);
//    skipSpace(src);
//    assert(*src == '(');
//    src++;
//    while (1) {
//      skipSpace(src);
//      if (*src == ')') break;
//      Frag arg(src);
//      assert(arg.type == IDENT);
//      src += arg.size;
//      Builder::appendArgumentToFunction(ret, arg.str);
//      skipSpace(src);
//      if (*src == ')') break;
//      if (*src == ',') {
//        src++;
//        continue;
//      }
//      abort();
//    }
//    src++;
//    Builder::setBlockContent(ret, parseBracketedBlock(src));
//    // TODO: parse expression?
//    return ret;
//  }

    // RSTODO
    fn parseVar(&mut self, _src: &mut *const u8, _seps: *const u8, _is_const: bool) -> Ref {
        panic!()
    }
//  NodeRef parseVar(char*& src, const char* seps, bool is_const) {
//    NodeRef ret = Builder::makeVar(is_const);
//    while (1) {
//      skipSpace(src);
//      if (*src == ';') break;
//      Frag name(src);
//      assert(name.type == IDENT);
//      NodeRef value;
//      src += name.size;
//      skipSpace(src);
//      if (*src == '=') {
//        src++;
//        skipSpace(src);
//        value = parseElement(src, ";,");
//      }
//      Builder::appendToVar(ret, name.str, value);
//      skipSpace(src);
//      if (*src == ';') break;
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
    fn parseReturn(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
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
    fn parseIf(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
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
    fn parseDo(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
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
    fn parseWhile(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseWhile(char*& src, const char* seps) {
//    NodeRef condition = parseParenned(src);
//    NodeRef body = parseMaybeBracketed(src, seps);
//    return Builder::makeWhile(condition, body);
//  }

    // RSTODO
    fn parseBreak(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseBreak(char*& src, const char* seps) {
//    skipSpace(src);
//    Frag next(src);
//    if (next.type == IDENT) src += next.size;
//    return Builder::makeBreak(next.type == IDENT ? next.str : IString());
//  }

    // RSTODO
    fn parseContinue(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseContinue(char*& src, const char* seps) {
//    skipSpace(src);
//    Frag next(src);
//    if (next.type == IDENT) src += next.size;
//    return Builder::makeContinue(next.type == IDENT ? next.str : IString());
//  }

    // RSTODO
    fn parseSwitch(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
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
    fn parseNew(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseNew(char*& src, const char* seps) {
//    return Builder::makeNew(parseElement(src, seps));
//  }

    // RSTODO
    fn parseAfterIdent(&mut self, _frag: &Frag, _src: &mut *const u8, _seps: *const u8) -> Ref {
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
    fn parseCall(&mut self, _target: Ref, _src: &mut *const u8) -> Ref {
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
    fn parseIndexing(&mut self, _target: Ref, _src: &mut *const u8) -> Ref {
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
    fn parseDotting(&mut self, _target: Ref, _src: &mut *const u8) -> Ref {
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
    fn parseAfterParen(&mut self, _src: &mut *const u8) -> Ref {
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
    fn parseAfterBrace(&mut self, _src: &mut *const u8) -> Ref {
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
    fn parseAfterCurly(&mut self, _src: &mut *const u8) -> Ref {
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
    fn makeBinary(_left: Ref, _op: IString, _right: Ref) -> Ref {
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
    fn parseExpression(&mut self, _initial: ExpressionElement, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseExpression(ExpressionElement initial, char*&src, const char* seps) {
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
    fn parseBlock(&mut self, _src: &mut *const u8, _seps: *const u8, _keywordSep1: Option<IString>, _keywordSep2: Option<IString>) -> Ref {
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
    fn parseBracketedBlock(&mut self, _src: &mut *const u8) -> Ref {
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
    fn parseElementOrStatement(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
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
    fn parseMaybeBracketed(&mut self, _src: &mut *const u8, _seps: *const u8) -> Ref {
        panic!()
    }
//  NodeRef parseMaybeBracketed(char*& src, const char *seps) {
//    skipSpace(src);
//    return *src == '{' ? parseBracketedBlock(src) : parseElementOrStatement(src, seps);
//  }

    // RSTODO
    fn parseParenned(&mut self, _src: &mut *const u8) -> Ref {
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
    fn parseToplevel(&mut self, _src: &mut *const u8) -> Ref {
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
    fn dump(&mut self, _msg: *const u8, _curr: *const u8) {
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
    fn dumpParts(_parts: Vec<Vec<ExpressionElement>>, _i: usize) {
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

