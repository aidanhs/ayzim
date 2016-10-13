// Pure parsing. Calls methods on a Builder (template argument) to actually
// construct the AST
//
// XXX All parsing methods assume they take ownership of the input string. This
// lets them reuse parts of it. You will segfault if the input string cannot be
// reused and written to.

// RSTODO: nom parser?

use std::ptr;
use std::slice;
use std::str;

use libc;
use libc::{c_char, c_int};

use phf;
use phf_builder;

use super::IString;
use super::cashew::AstNode;
use super::cashew::builder;
use super::num::{f64tou32, isInteger32};

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

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum OpClassTy {
    Binary = 0,
    Prefix = 1,
    Tertiary = 2,
}
pub struct OpClass {
    ops: phf::Set<IString>,
    rtl: bool,
    ty: OpClassTy,
}

impl OpClass {
    fn new(ops: phf::Set<IString>, rtl: bool, ty: OpClassTy) -> OpClass {
        OpClass { ops: ops, rtl: rtl, ty: ty }
    }

    pub fn getPrecedence(ty: OpClassTy, op: IString) -> usize {
        *PRECEDENCES[ty as usize].get(&op).unwrap()
    }

    pub fn getRtl(prec: usize) -> bool {
        OP_CLASSES[prec].rtl
    }
}

macro_rules! pp {
    { $p:ident += $off:expr } => {{ *$p = (*$p).offset($off as isize) }};
    { $p:ident + $off:expr } => {{ (*$p).offset($off as isize) }};
    { $p:ident[$off:expr] } => {{ *(*$p).offset($off as isize) }};
}
macro_rules! p {
    { $p:ident += $off:expr } => {{ $p = $p.offset($off as isize) }};
    { $p:ident + $off:expr } => {{ $p.offset($off as isize) }};
    { $p:ident[$off:expr] } => {{ *$p.offset($off as isize) }};
}

fn isIdentInit(x: u8) -> bool {
    (x >= b'a' && x <= b'z') || (x >= b'A' && x <= b'Z') || x == b'_' || x == b'$'
}
// RSTODO: use isDigit?
pub fn isIdentPart(x: u8) -> bool {
    isIdentInit(x) || (x >= b'0' && x <= b'9')
}
fn isSpace(x: u8) -> bool {
    // space, tab, linefeed/newline or return
    x == 32 || x == 9 || x == 10 || x == 13
}
fn isDigit(x: u8) -> bool {
    x >= b'0' && x <= b'9'
}
unsafe fn hasChar(mut list: *const u8, x: u8) -> bool {
    while p!{list[0]} != b'\0' {
        if p!{list[0]} == x {
            return true
        }
        p!{list+=1}
    }
    false
}

// not eq because float NaN is not reflexive
#[derive(PartialEq)]
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

    fn parse(&self) -> AstNode {
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
            if !b.contains(&b'.') && isInteger32(num) {
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
            p!{src+=is.len()};
            FragData::Operator(is)
        } else if hasChar(SEPARATORS.as_ptr(), p!{src[0]}) {
            let b = slice::from_raw_parts(src, 1);
            let s = str::from_utf8_unchecked(b);
            let is = IString::from(s);
            p!{src+=1};
            FragData::Separator(is)
        } else if p!{src[0]} == b'"' || p!{src[0]} == b'\'' {
            src = libc::strchr(p!{src+1} as *const c_char, p!{src[0]} as c_int) as *const _;
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

#[derive(Debug)]
enum ExprElt {
    Node(AstNode),
    Op(IString),
}

// parser

pub struct Parser {
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
    unsafe fn parseElement(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        //dump("parseElement", src);
        skipSpace(src);
        let frag = Frag::from_str(*src);
        pp!{src+=frag.size};
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

    unsafe fn parseAfterKeyword(&mut self, frag: &Frag, src: &mut *const u8, seps: *const u8) -> AstNode {
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
    unsafe fn parseFunction(&mut self, src: &mut *const u8, _seps: *const u8) -> AstNode {
        let name_str = match Frag::from_str(*src) {
            Frag { data: FragData::Ident(s), size: n } => { pp!{src+=n}; s },
            Frag { data: FragData::Separator(is!("(")), .. } => is!(""),
            _ => panic!(),
        };
        let mut ret = builder::makeFunction(name_str);
        skipSpace(src);
        assert!(pp!{src[0]} == b'(');
        pp!{src+=1};
        loop {
            skipSpace(src);
            if pp!{src[0]} == b')' { break }
            if let Frag { data: FragData::Ident(s), size: n } = Frag::from_str(*src) {
                pp!{src+=n};
                builder::appendArgumentToFunction(&mut ret, s)
            } else { panic!() }
            skipSpace(src);
            match pp!{src[0]} {
                b')' => break,
                b',' => { pp!{src+=1}; continue },
                _ => panic!(),
            }
        }
        pp!{src+=1};
        builder::setBlockContent(&mut ret, self.parseBracketedBlock(src));
        // TODO: parse expression?
        ret
    }

    // RSTODO: remove seps?
    unsafe fn parseVar(&mut self, src: &mut *const u8, _seps: *const u8, is_const: bool) -> AstNode {
        let mut ret = builder::makeVar(is_const);
        loop {
            skipSpace(src);
            if pp!{src[0]} == b';' { break }
            let name_str = if let Frag { data: FragData::Ident(s), size: n } = Frag::from_str(*src) {
                pp!{src+=n};
                s
            } else { panic!() };
            skipSpace(src);
            let mut value = None;
            if pp!{src[0]} == b'=' {
                pp!{src+=1};
                skipSpace(src);
                value = Some(self.parseElement(src, b";,\0".as_ptr()))
            }
            builder::appendToVar(&mut ret, name_str, value);
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

    unsafe fn parseReturn(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        skipSpace(src);
        let mut value = None;
        if !hasChar(seps, pp!{src[0]}) {
            value = Some(self.parseElement(src, seps))
        }
        assert!(hasChar(seps, pp!{src[0]}));
        if pp!{src[0]} == b';' { pp!{src+=1} }
        builder::makeReturn(value)
    }

    unsafe fn parseIf(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        let condition = self.parseParenned(src);
        let ifTrue = self.parseMaybeBracketed(src, seps);
        skipSpace(src);
        let mut ifFalse = None;
        if !hasChar(seps, pp!{src[0]}) {
            let next = Frag::from_str(*src);
            if let Frag { data: FragData::Keyword(is!("else")), size: n } = next {
                pp!{src+=n};
                ifFalse = Some(self.parseMaybeBracketed(src, seps))
            }
        }
        builder::makeIf(condition, ifTrue, ifFalse)
    }

    unsafe fn parseDo(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        let body = self.parseMaybeBracketed(src, seps);
        skipSpace(src);
        let next = Frag::from_str(*src);
        if let Frag { data: FragData::Keyword(is!("while")), size: n } = next {
            pp!{src+=n};
        } else { panic!() }
        let condition = self.parseParenned(src);
        builder::makeDo(body, condition)
    }

    unsafe fn parseWhile(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        let condition = self.parseParenned(src);
        let body = self.parseMaybeBracketed(src, seps);
        builder::makeWhile(condition, body)
    }

    // RSTODO: remove seps?
    unsafe fn parseBreak(&mut self, src: &mut *const u8, _seps: *const u8) -> AstNode {
        skipSpace(src);
        let next = Frag::from_str(*src);
        let mut arg = None;
        if let Frag { data: FragData::Ident(s), size: n } = next {
            pp!{src+=n};
            arg = Some(s)
        }
        builder::makeBreak(arg)
    }

    // RSTODO: remove seps?
    unsafe fn parseContinue(&mut self, src: &mut *const u8, _seps: *const u8) -> AstNode {
        skipSpace(src);
        let next = Frag::from_str(*src);
        let mut arg = None;
        if let Frag { data: FragData::Ident(s), size: n } = next {
            pp!{src+=n};
            arg = Some(s)
        }
        builder::makeContinue(arg)

    }

    // RSTODO: remove seps?
    unsafe fn parseSwitch(&mut self, src: &mut *const u8, _seps: *const u8) -> AstNode {
        let mut ret = builder::makeSwitch(self.parseParenned(src));
        skipSpace(src);
        assert!(pp!{src[0]} == b'{');
        pp!{src+=1};
        loop {
            // find all cases and possibly a default
            skipSpace(src);
            if pp!{src[0]} == b'}' { break }
            let next = Frag::from_str(*src);
            match next {
                Frag { data: FragData::Keyword(is!("case")), size: n } => {
                    pp!{src+=n};
                    skipSpace(src);
                    let value = Frag::from_str(*src);
                    let arg = if value.isNumber() {
                        pp!{src+=value.size};
                        value.parse()
                    } else {
                        assert!(value.data == FragData::Operator(is!("-")));
                        pp!{src+=value.size};
                        skipSpace(src);
                        let value2 = Frag::from_str(*src);
                        assert!(value2.isNumber());
                        pp!{src+=value2.size};
                        builder::makePrefix(is!("-"), value2.parse())
                    };
                    builder::appendCaseToSwitch(&mut ret, arg);
                    skipSpace(src);
                    assert!(pp!{src[0]} == b':');
                    pp!{src+=1};
                    continue
                },
                Frag { data: FragData::Keyword(is!("default")), size: n } => {
                    pp!{src+=n};
                    builder::appendDefaultToSwitch(&mut ret);
                    skipSpace(src);
                    assert!(pp!{src[0]} == b':');
                    pp!{src+=1};
                    continue
                },
                // otherwise, may be some keyword that happens to start a block
                // (e.g. case 1: _return_ 5)
                _ => ()
            }
            // not case X: or default: or }, so must be some code
            skipSpace(src);
            let explicitBlock = pp!{src[0]} == b'{';
            let subBlock = if explicitBlock {
                self.parseBracketedBlock(src)
            } else {
                self.parseBlock(src, b";}\0".as_ptr(), Some(is!("case")), Some(is!("default")))
            };
            builder::appendCodeToSwitch(&mut ret, subBlock, explicitBlock);
        }
        skipSpace(src);
        assert!(pp!{src[0]} == b'}');
        pp!{src+=1};
        ret
    }

    unsafe fn parseNew(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        builder::makeNew(self.parseElement(src, seps))
    }

    // RSTODO
    unsafe fn parseAfterIdent(&mut self, frag: &Frag, src: &mut *const u8, seps: *const u8) -> AstNode {
        skipSpace(src);
        match pp!{src[0]} {
            b'(' => {
                let exprelt = ExprElt::Node(self.parseCall(frag.parse(), src));
                self.parseExpression(exprelt, src, seps)
            },
            b'[' => {
                let exprelt = ExprElt::Node(self.parseIndexing(frag.parse(), src));
                self.parseExpression(exprelt, src, seps)
            },
            b':' if self.expressionPartsStack.last().unwrap().is_empty() => {
                pp!{src+=1};
                skipSpace(src);
                let inner = if pp!{src[0]} == b'{' {
                    // context lets us know this is not an object, but a block
                    self.parseBracketedBlock(src)
                } else {
                    self.parseElement(src, seps)
                };
                builder::makeLabel(frag.getStr(), inner)
            },
            b'.' => {
                let exprelt = ExprElt::Node(self.parseDotting(frag.parse(), src));
                self.parseExpression(exprelt, src, seps)
            },
            _ => self.parseExpression(ExprElt::Node(frag.parse()), src, seps),
        }
    }

    unsafe fn parseCall(&mut self, target: AstNode, src: &mut *const u8) -> AstNode {
        self.expressionPartsStack.push(vec![]);
        assert!(pp!{src[0]} == b'(');
        pp!{src+=1};
        let mut ret = builder::makeCall(target);
        loop {
            skipSpace(src);
            if pp!{src[0]} == b')' { break }
            builder::appendToCall(&mut ret, self.parseElement(src, b",)\0".as_ptr()));
            skipSpace(src);
            if pp!{src[0]} == b')' { break }
            if pp!{src[0]} == b',' { pp!{src+=1}; continue }
            panic!()
        }
        pp!{src+=1};
        assert!(self.expressionPartsStack.pop().unwrap().len() == 0);
        ret
    }

    unsafe fn parseIndexing(&mut self, target: AstNode, src: &mut *const u8) -> AstNode {
        self.expressionPartsStack.push(vec![]);
        assert!(pp!{src[0]} == b'[');
        pp!{src+=1};
        let elt = self.parseElement(src, b"]\0".as_ptr());
        let ret = builder::makeIndexing(target, elt);
        skipSpace(src);
        assert!(pp!{src[0]} == b']');
        pp!{src+=1};
        assert!(self.expressionPartsStack.pop().unwrap().len() == 0);
        ret
    }

    unsafe fn parseDotting(&mut self, target: AstNode, src: &mut *const u8) -> AstNode {
        assert!(pp!{src[0]} == b'[');
        pp!{src+=1};
        if let Frag { data: FragData::Ident(s), size: n } = Frag::from_str(*src) {
            pp!{src+=n};
            builder::makeDot(target, s)
        } else { panic!() }
    }

    unsafe fn parseAfterParen(&mut self, src: &mut *const u8) -> AstNode {
        self.expressionPartsStack.push(vec![]);
        skipSpace(src);
        let ret = self.parseElement(src, b")\0".as_ptr());
        skipSpace(src);
        assert!(pp!{src[0]} == b')');
        pp!{src+=1};
        assert!(self.expressionPartsStack.pop().unwrap().len() == 0);
        ret
    }

    // RSTODO: needs expressionPartsStack pop?
    unsafe fn parseAfterBrace(&mut self, src: &mut *const u8) -> AstNode {
        self.expressionPartsStack.push(vec![]);
        let mut ret = builder::makeArray();
        loop {
            skipSpace(src);
            assert!(pp!{src[0]} != b'\0');
            if pp!{src[0]} == b']' { break }
            builder::appendToArray(&mut ret, self.parseElement(src, b",]\0".as_ptr()));
            skipSpace(src);
            if pp!{src[0]} == b']' { break }
            if pp!{src[0]} == b',' { pp!{src+=1}; continue }
            panic!()
        }
        pp!{src+=1};
        ret
    }

    // RSTODO: needs expressionPartsStack pop?
    unsafe fn parseAfterCurly(&mut self, src: &mut *const u8) -> AstNode {
        self.expressionPartsStack.push(vec![]);
        let mut ret = builder::makeObject();
        loop {
            skipSpace(src);
            assert!(pp!{src[0]} != b'\0');
            if pp!{src[0]} == b'}' { break }
            let (s, n) = match Frag::from_str(*src) { // key
                Frag { data: FragData::Ident(s), size: n } |
                Frag { data: FragData::String(s), size: n } => (s, n),
                _ => panic!(),
            };
            pp!{src+=n};
            skipSpace(src);
            assert!(pp!{src[0]} == b':');
            pp!{src+=1};
            let value = self.parseElement(src, b",}\0".as_ptr());
            builder::appendToObject(&mut ret, s, value);
            skipSpace(src);
            if pp!{src[0]} == b'}' { break }
            if pp!{src[0]} == b',' { pp!{src+=1}; continue }
            panic!()
        }
        pp!{src+=1};
        ret
    }

    unsafe fn makeBinary(left: AstNode, op: IString, right: AstNode) -> AstNode {
        if op == is!(".") {
            builder::makeDotAstNode(left, right)
        } else {
            builder::makeBinary(left, op, right)
        }
    }

    unsafe fn parseExpression(&mut self, initial: ExprElt, src: &mut *const u8, seps: *const u8) -> AstNode {
        //dump("parseExpression", src);
        // RSTODO: this function is to make it less ugly to work around rust
        // lexical lifetimes
        fn getParts(s: &mut Parser) -> &mut Vec<ExprElt> {
            s.expressionPartsStack.last_mut().unwrap()
        }
        skipSpace(src);
        if pp!{src[0]} == b'\0' || hasChar(seps, pp!{src[0]}) {
            let parts = getParts(self);
            if !parts.is_empty() {
                // RSTODO: This is ridiculously unsafe but is needed because of
                // the way the expression stack works. When parseExpression is
                // called with an empty top level of the stack, the bit between
                // 'let top' and 'let last' begins the population of the stack
                // level. The 'let last = parseElement' then recursively calls
                // down back into parseExpression, building up the stack and
                // until we hit *this* line. All of the parseExpressions but
                // the top level one then return (because !top) and top level
                // sorts it all out.
                // Note that this ptr::read is crucially coupled with the
                // mem::forget near 'let last'.
                // https://github.com/kripken/cashew/commit/a2f527c1597cdbe0342cb4154465023159832518
                parts.push(::std::ptr::read(&initial)); // cherry on top of the cake
            }
            let node = if let ExprElt::Node(n) = initial { n } else { panic!() };
            return node
        }
        let top;
        if let ExprElt::Node(node) = initial {
            let next = Frag::from_str(*src);
            if let Frag { data: FragData::Operator(s), size: n } = next {
                let parts = getParts(self);
                top = parts.is_empty();
                parts.push(ExprElt::Node(node));
                pp!{src+=n};
                parts.push(ExprElt::Op(s))
            } else {
                let initial = ExprElt::Node(match pp!{src[0]} {
                    b'(' => self.parseCall(node, src),
                    b'[' => self.parseIndexing(node, src),
                    _ => {
                        //self.dump("bad parseExpression state", *src);
                        panic!("bad parseExpression state")
                    },
                });
                return self.parseExpression(initial, src, seps)
            }
        } else {
            let parts = getParts(self);
            top = parts.is_empty();
            parts.push(initial)
        }
        let last = self.parseElement(src, seps);
        if !top { return last }
        ::std::mem::forget(last);
        let parts = getParts(self); // parts may have been invalidated by that call
        // we are the toplevel. sort it all out
        // collapse right to left, highest priority first
        //dumpParts(parts, 0);
        for ops in OP_CLASSES.iter() {
            // RSTODO: consider unifying rtl and ltr
            if ops.rtl {
                // right to left
                cfor!{let mut i = parts.len()-1; /* cond */; if i == 0 { break }, i -= 1; {
                    let op = match parts[i] {
                        ExprElt::Node(_) => continue,
                        ExprElt::Op(ref op) => op.clone(),
                    };
                    if !ops.ops.contains(&op) { continue }
                    if ops.ty == OpClassTy::Binary && i > 0 && i < parts.len()-1 {
                        let part2 = parts.remove(i+1);
                        let part1 = parts.remove(i-1);
                        let (n1, n2) = match (part1, part2) {
                            (ExprElt::Node(n1), ExprElt::Node(n2)) => (n1, n2),
                            _ => panic!("not both nodes in rtl binary"),
                        };
                        // RSTODO: if assigned at i-1, only need one drain?
                        parts[i-1] = ExprElt::Node(Self::makeBinary(n1, op, n2));
                        // RSTODO: could optimise here by decrementing to avoid
                        // reprocessing? Note the unfortunate asymmetry with ltr
                    } else if ops.ty == OpClassTy::Prefix && i < parts.len()-1 {
                        if i > 0 {
                            // cannot apply prefix operator if it would join
                            // two nodes
                            if let ExprElt::Node(_) = parts[i-1] { continue }
                        }
                        let n1 = match parts.remove(i+1) {
                            ExprElt::Node(n1) => n1,
                            _ => panic!("not node in rtl prefix"),
                        };
                        parts[i] = ExprElt::Node(builder::makePrefix(op, n1));
                    } else if ops.ty == OpClassTy::Tertiary {
                        // we must be at  X ? Y : Z
                        //                      ^
                        //dumpParts(parts, i);
                        if op != is!(":") { continue }
                        assert!(i < parts.len()-1 && i >= 3);
                        match parts[i-2] {
                            ExprElt::Op(is!("?")) => (),
                            ExprElt::Op(_) => continue,
                            ExprElt::Node(_) => panic!("node in rtl tertiary"),
                        }
                        let part3 = parts.remove(i+1);
                        let part2 = parts.remove(i-1);
                        let _ = parts.remove(i-2);
                        let part1 = parts.remove(i-3);
                        let (n1, n2, n3) = match (part1, part2, part3) {
                            (ExprElt::Node(n1), ExprElt::Node(n2), ExprElt::Node(n3)) => (n1, n2, n3),
                            _ => panic!("not all three nodes in rtl tertiary"),
                        };
                        parts[i-3] = ExprElt::Node(builder::makeConditional(n1, n2, n3));
                        i = parts.len();
                    } // TODO: postfix
                }}
            } else {
                // left to right
                cfor!{let mut i = 0; i < parts.len(); i += 1; {
                    let op = match parts[i] {
                        ExprElt::Node(_) => continue,
                        ExprElt::Op(ref op) => op.clone(),
                    };
                    if !ops.ops.contains(&op) { continue }
                    if ops.ty == OpClassTy::Binary && i > 0 && i < parts.len()-1 {
                        let part2 = parts.remove(i+1);
                        let part1 = parts.remove(i-1);
                        let (n1, n2) = match (part1, part2) {
                            (ExprElt::Node(n1), ExprElt::Node(n2)) => (n1, n2),
                            _ => panic!("not both nodes in ltr binary"),
                        };
                        // RSTODO: if assigned at i-1, only need one drain?
                        parts[i-1] = ExprElt::Node(Self::makeBinary(n1, op, n2));
                        i -= 1;
                    } else if ops.ty == OpClassTy::Prefix && i < parts.len()-1 {
                        if i > 0 {
                            // cannot apply prefix operator if it would join
                            // two nodes
                            if let ExprElt::Node(_) = parts[i-1] { continue }
                        }
                        let n1 = match parts.remove(i+1) {
                            ExprElt::Node(n1) => n1,
                            _ => panic!("not node in ltr prefix"),
                        };
                        parts[i] = ExprElt::Node(builder::makePrefix(op, n1));
                        // allow a previous prefix operator to cascade
                        i = if i > 2 { i-2 } else { 0 };
                    } // TODO: tertiary, postfix
                }}
            }
        }
        let part = parts.pop().unwrap();
        assert!(parts.is_empty());
        if let ExprElt::Node(n) = part { n } else { panic!() }
    }

    // Parses a block of code (e.g. a bunch of statements inside {,}, or the top level of o file)
    unsafe fn parseBlock(&mut self, src: &mut *const u8, seps: *const u8, keywordSep1: Option<IString>, keywordSep2: Option<IString>) -> AstNode {
        let mut block = builder::makeBlock();
        //dump("parseBlock", src);
        loop {
            skipSpace(src);
            if pp!{src[0]} == b'\0' { break }
            if pp!{src[0]} == b';' {
                pp!{src+=1}; // skip a statement in this block
                continue
            }
            if hasChar(seps, pp!{src[0]}) { break }
            // RSTODO: combine these two conditions?
            if let Some(ref ks) = keywordSep1 {
                assert!(*ks != is!(""));
                let next = Frag::from_str(*src);
                if FragData::Keyword(ks.clone()) == next.data { break }
            }
            if let Some(ref ks) = keywordSep2 {
                assert!(*ks != is!(""));
                let next = Frag::from_str(*src);
                if FragData::Keyword(ks.clone()) == next.data { break }
            }
            let element = self.parseElementOrStatement(src, seps);
            builder::appendToBlock(&mut block, element);
        }
        block
    }

    unsafe fn parseBracketedBlock(&mut self, src: &mut *const u8) -> AstNode {
        skipSpace(src);
        assert!(pp!{src[0]} == b'{');
        pp!{src+=1};
        // the two are not symmetrical, ; is just internally separating, } is
        // the final one - parseBlock knows all this
        let block = self.parseBlock(src, b";}\0".as_ptr(), None, None);
        assert!(pp!{src[0]} == b'}');
        pp!{src+=1};
        block
    }

    unsafe fn parseElementOrStatement(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        skipSpace(src);
        if pp!{src[0]} == b';' {
            pp!{src+=1};
        }
        if pp!{src[0]} == b'{' { // detect a trivial {} in a statement context
            let before = *src;
            pp!{src+=1};
            skipSpace(src);
            if pp!{src[0]} == b'}' {
                pp!{src+=1};
                // we don't need the brackets here, but oh well
                return builder::makeBlock()
            }
            *src = before;
        }
        let mut ret = self.parseElement(src, seps);
        skipSpace(src);
        if pp!{src[0]} == b';' {
            ret = builder::makeStatement(ret);
            pp!{src+=1};
        }
        ret
    }

    unsafe fn parseMaybeBracketed(&mut self, src: &mut *const u8, seps: *const u8) -> AstNode {
        skipSpace(src);
        if pp!{src[0]} == b'{' {
            self.parseBracketedBlock(src)
        } else {
            self.parseElementOrStatement(src, seps)
        }
    }

    unsafe fn parseParenned(&mut self, src: &mut *const u8) -> AstNode {
        skipSpace(src);
        assert!(pp!{src[0]} == b'(');
        pp!{src+=1};
        let ret = self.parseElement(src, b")\0".as_ptr());
        skipSpace(src);
        assert!(pp!{src[0]} == b')');
        pp!{src+=1};
        ret
    }

    pub fn new() -> Parser {
        Parser {
            expressionPartsStack: vec![vec![]],
            allSource: ptr::null(),
            allSize: 0,
        }
    }

    pub unsafe fn parseToplevel(&mut self, src: *const u8) -> AstNode {
        self.allSource = src;
        self.allSize = libc::strlen(src as *const i8);
        let mut toplevel = builder::makeToplevel();
        let mut cursrc = src;
        let block = self.parseBlock(&mut cursrc, b";\0".as_ptr(), None, None);
        builder::setBlockContent(&mut toplevel, block);
        toplevel
    }

    // Debugging

    // RSTODO
    //unsafe fn dump(&mut self, _msg: &str, _curr: *const u8) {
    //    panic!()
    //}
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
    //unsafe fn dumpParts(_parts: Vec<Vec<ExprElt>>, _i: usize) {
    //    panic!()
    //}
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

