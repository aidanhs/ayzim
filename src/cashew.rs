use std::collections::HashMap;
use std::io::Write;
use std::io;
use std::isize;
use std::iter;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::str;
use std::u64;

use odds::vec::VecExt;
use serde;
use serde_json;
use smallvec::SmallVec;
use typed_arena;

use super::IString;
use super::num::{f64toi64, f64tou64, isInteger, isInteger64};
use super::parser::{OpClass, OpClassTy};
use super::parser::isIdentPart;

// RSTODO: totally get rid of Ref?
#[derive(Copy, Clone, Debug)]
pub struct Ref {
    inst: *mut Value,
}

impl Ref {
    fn new(v: *mut Value) -> Ref { // can be null
        Ref { inst: v }
    }
    fn get_val(&self) -> &Value {
        unsafe { &(*self.inst) }
    }
    fn get_val_mut(&mut self) -> &mut Value {
        unsafe { &mut (*self.inst) }
    }
    pub fn is_something(&self) -> bool {
        self.inst != ptr::null_mut() && !self.isNull()
    }
// RSTODO
//  Value& operator*() { return *inst; }
//  Value* operator->() { return inst; }
//  Ref& operator[](unsigned x);
//  Ref& operator[](IString x);
//
//  // special conveniences
//  bool operator==(const char *str); // comparison to string, which is by value
//  bool operator!=(const char *str);
//  bool operator==(const IString &str);
//  bool operator!=(const IString &str);
//  bool operator==(double d) { abort(); return false; } // prevent Ref == number, which is potentially ambiguous; use ->getNumber() == number
//  bool operator==(Ref other);
//  bool operator!(); // check if null, in effect
//};
}

impl Deref for Ref {
    type Target = Value;

    fn deref(&self) -> &Value {
        self.get_val()
    }
}
impl DerefMut for Ref {
    fn deref_mut(&mut self) -> &mut Value {
        self.get_val_mut()
    }
}
// RSTODO: not really sync
unsafe impl Sync for Ref {}

const EMPTYREF: Ref = Ref { inst: ptr::null_mut() };

// Arena allocation, free it all on process exit

// http://contain-rs.github.io/raw-vec/raw_vec/struct.RawVec.html
// RSTODO: is the value arena actually better than jemalloc?
// RSTODO: Would an array arena be good? It would add extra indirection
const ARENA_CHUNK_SIZE: usize = 1000;
pub struct Arena {
    arena: typed_arena::Arena<Value>,
    //arr_arena: typed_arena::Arena<ArrayStorage>,
    //chunks: Vec<Box<[Value; ARENA_CHUNK_SIZE]>>,
    //index: usize, // in last chunk
    //arr_chunks: Vec<Box<[ArrayStorage; ARENA_CHUNK_SIZE]>>,
    //arr_index: usize,
}

impl Arena {
    fn new() -> Arena {
        //Arena { chunks: vec![], index: 0, arr_chunks: vec![], arr_index: 0 }
        Arena {
            arena: typed_arena::Arena::with_capacity(1000),
            //arr_arena: typed_arena::Arena::with_capacity(1000),
        }
    }
    // RSTODO: placeholder
    fn allocArray(&self) -> ArrayStorage {
        //self.arr_arena.alloc(ArrayStorage::new())
        vec![]
    }
    pub fn alloc(&self) -> Ref {
        Ref::new(self.arena.alloc(Value::new()))
    }
}

// RSTODO: remove
// this allows the lazy_static
unsafe impl Sync for Arena {}

lazy_static! {
    pub static ref ARENA: Arena = Arena::new();
}

pub type ArrayStorage = Vec<Ref>;
pub type ObjectStorage = HashMap<IString, Ref>;

// RSTODO: why can't expr be tt?
macro_rules! an {
    { $variant:ident( $( $x:expr ),* ) } => {
        Box::new(AstValue::$variant( $( $x ),* ))
    };
}

macro_rules! __ifletify {
    // Begin
    { ($inexpr:expr) $x:ident($( $ts:ty ),+) } => {
        __ifletify!{ in ($inexpr) $x v () ($( $ts, )+) }
    };
    { ref ($inexpr:expr) $x:ident($( $ts:ty ),+) } => {
        __ifletify!{ inref ($inexpr) $x v () ($( $ts, )+) }
    };
    { mut ($inexpr:expr) $x:ident($( $ts:ty ),+) } => {
        __ifletify!{ inmut ($inexpr) $x v () ($( $ts, )+) }
    };
    // End
    { in ($inexpr:expr) $x:ident $v:ident ($( $vs:ident, )+) () } => {
        if let $x($( $vs ),+) = $inexpr { ($( $vs ),+,) } else { panic!() }
    };
    { inref ($inexpr:expr) $x:ident $v:ident ($( $vs:ident, )+) () } => {
        if let $x($( ref $vs ),+) = $inexpr { ($( $vs ),+,) } else { panic!() }
    };
    { inmut ($inexpr:expr) $x:ident $v:ident ($( $vs:ident, )+) () } => {
        if let $x($( ref mut $vs ),+) = $inexpr { ($( $vs ),+,) } else { panic!() }
    };
    // Transform each type in the enum variant tuple into a fresh variable
    { in ($inexpr:expr) $x:ident $v:ident ($( $vs:ident, )*) ($t:ty, $( $ts:ty, )*) } => {
        interpolate_idents!{ __ifletify!{ in ($inexpr) $x [$v v] ($v, $( $vs, )*) ($( $ts, )*) } }
    };
    { inref ($inexpr:expr) $x:ident $v:ident ($( $vs:ident, )*) ($t:ty, $( $ts:ty, )*) } => {
        interpolate_idents!{ __ifletify!{ inref ($inexpr) $x [$v v] ($v, $( $vs, )*) ($( $ts, )*) } }
    };
    { inmut ($inexpr:expr) $x:ident $v:ident ($( $vs:ident, )*) ($t:ty, $( $ts:ty, )*) } => {
        interpolate_idents!{ __ifletify!{ inmut ($inexpr) $x [$v v] ($v, $( $vs, )*) ($( $ts, )*) } }
    };
}
macro_rules! AstValue {
    { $( $x:ident($( $y:ty ),+), )+ } => {
        #[derive(Debug, PartialEq)]
        pub enum AstValue {
            $(
                $x($( $y ),*),
            )*
        }
        // RSTODO: this works because NaN is parsed as an ident rather than a
        // num. However, the presence of f64 in Num means Eq can't be derived.
        impl Eq for AstValue{}
        impl AstValue {
            $( interpolate_idents!{
                pub fn [is $x](&self) -> bool {
                    if let $x(..) = *self { true } else { false }
                }
                pub fn [into $x](self) -> ($( $y ),*,) {
                    __ifletify!{ (self) $x($( $y ),+) }
                }
                pub fn [get $x](&self) -> ($( &$y ),*,) {
                    __ifletify!{ ref (*self) $x($( $y ),+) }
                }
                pub fn [getMut $x](&mut self) -> ($( &mut $y ),*,) {
                    __ifletify!{ mut (*self) $x($( $y ),+) }
                }
            } )*
        }
    }
}

use self::AstValue::*;
pub type AstNode = Box<AstValue>;
// Reduces AstValue size from 64 bytes to 32
pub type AstVec<T> = Box<Vec<T>>;
AstValue!{
    Array(AstVec<AstNode>),            // [item]
    // RSTODO: https://github.com/kripken/emscripten/issues/4367
    Assign(bool, AstNode, AstNode),    // boo(true), left, right
    Binary(IString, AstNode, AstNode), // op, left, right
    Block(AstVec<AstNode>),            // [stat]
    Break(Option<IString>),            // Option<label>
    Call(AstNode, AstVec<AstNode>),    // fnexpr, [param]
    Conditional(AstNode, AstNode, AstNode), // cond, iftrue, iffalse
    Continue(Option<IString>),         // Option<label>
    Defun(IString, AstVec<IString>, AstVec<AstNode>), // fname, [arg], [stat]
    Do(AstNode, AstNode),              // condition, body
    Dot(AstNode, IString),             // obj, key
    If(AstNode, AstNode, Option<AstNode>), // cond, iftrue, Option<iffalse>
    Label(IString, AstNode),           // label, body
    Name(IString),                     // name
    New(AstNode),                      // call
    Num(f64),                          // num(number)
    Object(AstVec<(IString, AstNode)>), // [key, value]
    Return(Option<AstNode>),           // Option<retval>
    Seq(AstNode, AstNode),             // left, right
    Stat(AstNode),                     // stat
    String(IString),                   // string
    Sub(AstNode, AstNode),             // target, index
    Switch(AstNode, AstVec<(Option<AstNode>, Vec<AstNode>)>), // input, [(case|default, [stat|oneblock]]
    Toplevel(AstVec<AstNode>),         // [stat]
    UnaryPrefix(IString, AstNode),     // op, right
    Var(AstVec<(IString, Option<AstNode>)>), // [(name, Option<value>]
    While(AstNode, AstNode),           // condition, body
}

impl AstValue {
    pub fn from_ref(inref: Ref) -> AstNode {
        fn p(r: Ref) -> AstNode { AstValue::from_ref(r) } // parse
        fn b<T>(v: T) -> Box<T> { Box::new(v) } // box
        fn mkarr(r: Ref) -> Vec<AstNode> {
            r.getArray().iter().map(|&e| p(e)).collect()
        }
        fn maybe_parse(r: Ref) -> Option<AstNode> {
            if r.isNull() { None } else { Some(p(r)) }
        }
        fn mklabel(label: Ref) -> Option<IString> {
            if label.isNull() { None } else { Some(label.getIString()) }
        }
        let refarr = inref.getArray();
        Box::new(match (refarr[0].getIString(), &refarr[1..]) {
            (is!("array"), &[arr]) => Array(b(mkarr(arr))),
            (is!("assign"), &[b, left, right]) => Assign(b.getBool(), p(left), p(right)),
            (is!("binary"), &[op, left, right]) => Binary(op.getIString(), p(left), p(right)),
            (is!("block"), &[stats]) => Block(b(mkarr(stats))),
            (is!("break"), &[label]) => Break(mklabel(label)),
            (is!("call"), &[fnexpr, params]) => Call(p(fnexpr), b(mkarr(params))),
            (is!("conditional"), &[cond, iftrue, iffalse]) => Conditional(p(cond), p(iftrue), p(iffalse)),
            (is!("continue"), &[label]) => Continue(mklabel(label)),
            (is!("defun"), &[fnname, params, stats]) => Defun(fnname.getIString(), b(params.getArray().iter().map(|r| r.getIString()).collect()), b(mkarr(stats))),
            (is!("do"), &[cond, body]) => Do(p(cond), p(body)),
            (is!("dot"), &[obj, key]) => Dot(p(obj), key.getIString()),
            (is!("if"), &[cond, iftrue, maybeiffalse]) => If(p(cond), p(iftrue), maybe_parse(maybeiffalse)),
            (is!("label"), &[label, body]) => Label(label.getIString(), p(body)),
            (is!("name"), &[name]) => Name(name.getIString()),
            (is!("new"), &[call]) => New(p(call)),
            (is!("num"), &[num]) => Num(num.getNumber()),
            (is!("object"), &[keyvals]) => Object(b(keyvals.getArray().iter().map(|kv| { (kv.get(0).getIString(), p(kv.get(1))) }).collect())),
            (is!("return"), &[retval]) => Return(maybe_parse(retval)),
            (is!("seq"), &[left, right]) => Seq(p(left), p(right)),
            (is!("stat"), &[stat]) => Stat(p(stat)),
            (is!("string"), &[string]) => String(string.getIString()),
            (is!("sub"), &[target, index]) => Sub(p(target), p(index)),
            (is!("switch"), &[input, cases]) => Switch(p(input), b(cases.getArray().iter().map(|casedef| { (maybe_parse(casedef.get(0)), mkarr(casedef.get(1))) }).collect())),
            (is!("toplevel"), &[stats]) => Toplevel(b(mkarr(stats))),
            (is!("unary-prefix"), &[op, right]) => UnaryPrefix(op.getIString(), p(right)),
            (is!("var"), &[vardefs]) => Var(b(vardefs.getArray().iter().map(|vardef| { (vardef.get(0).getIString(), maybe_parse(vardef.get(1))) }).collect())),
            (is!("while"), &[condition, body]) => While(p(condition), p(body)),
            _ => panic!(),
        })
    }

    fn children<'a, 'b: 'a, I>(&'a mut self) -> Box<Iterator<Item=&'a mut AstNode> + 'a> {
        macro_rules! b {
            ($e: expr) => (Box::new($e));
        };
        match *self {
            Array(ref mut nodes) => b!(nodes.iter_mut()),
            Assign(_, ref mut left, ref mut right) => b!(vec![left, right].into_iter()),
            Binary(_, ref mut left, ref mut right) => b!(vec![left, right].into_iter()),
            Block(ref mut stats) => b!(stats.iter_mut()),
            Break(_) => b!(iter::empty()),
            Call(ref mut fnexpr, ref mut params) => b!(iter::once(fnexpr).chain(params.iter_mut())),
            Conditional(ref mut cond, ref mut iftrue, ref mut iffalse) => b!(vec![cond, iftrue, iffalse].into_iter()),
            Continue(_) => b!(iter::empty()),
            Defun(_, _, ref mut stats) => b!(stats.iter_mut()),
            Do(ref mut cond, ref mut body) => b!(vec![cond, body].into_iter()),
            Dot(ref mut obj, _) => b!(iter::once(obj)),
            If(ref mut cond, ref mut iftrue, ref mut maybeiffalse) => {
                let it = vec![cond, iftrue].into_iter();
                if let Some(ref mut n) = *maybeiffalse { b!(it.chain(iter::once(n))) } else { b!(it.chain(iter::empty())) }
            },
            Label(_, ref mut body) => b!(iter::once(body)),
            Name(_) => b!(iter::empty()),
            New(ref mut call) => b!(iter::once(call)),
            Num(_) => b!(iter::empty()),
            Object(ref mut keyvals) => b!(keyvals.iter_mut().map(|kv| &mut kv.1)),
            Return(ref mut retval) => if let Some(ref mut rv) = *retval { b!(iter::once(rv)) } else { b!(iter::empty()) },
            Seq(ref mut left, ref mut right) => b!(vec![left, right].into_iter()),
            Stat(ref mut stat) => b!(iter::once(stat)),
            String(_) => b!(iter::empty()),
            Sub(ref mut target, ref mut index) => b!(vec![target, index].into_iter()),
            Switch(ref mut input, ref mut cases) => {
                let it = iter::once(input);
                let casenodes = cases.iter_mut().flat_map(|&mut (ref mut case, ref mut block)| {
                    let initial = if let Some(ref mut c) = *case { vec![c] } else { vec![] }.into_iter();
                    initial.chain(block.iter_mut())
                });
                b!(it.chain(casenodes))
            },
            Toplevel(ref mut stats) => b!(stats.iter_mut()),
            UnaryPrefix(_, ref mut right) => b!(iter::once(right)),
            Var(ref mut vars) => b!(vars.iter_mut().filter_map(|var| var.1.as_mut())),
            While(ref mut cond, ref mut body) => b!(vec![cond, body].into_iter()),
        }
    }

    pub fn stringify<T>(&self, out: &mut T, pretty: bool) where T: Write {
        let outstr = if pretty {
            serde_json::ser::to_string_pretty(self)
        } else {
            serde_json::ser::to_string(self)
        }.unwrap();
        out.write(outstr.as_bytes()).unwrap();
    }
}

impl serde::Serialize for AstValue {
    fn serialize<S>(&self, s: &mut S) -> Result<(), S::Error> where S: serde::Serializer {
        macro_rules! s {
            ($( $e: expr ),+) => (($( $e ),+).serialize(s));
        };
        match *self {
            Array(ref nodes) => s!("array", nodes),
            Assign(ref b, ref left, ref right) => s!("assign", b, left, right),
            Binary(ref op, ref left, ref right) => s!("binary", op, left, right),
            Block(ref stats) => s!("block", stats),
            Break(ref label) => s!("break", label),
            Call(ref fnexpr, ref params) => s!("call", fnexpr, params),
            Conditional(ref cond, ref iftrue, ref iffalse) => s!("conditional", cond, iftrue, iffalse),
            Continue(ref label) => s!("continue", label),
            Defun(ref fname, ref args, ref stats) => s!("defun", fname, args, stats),
            Do(ref cond, ref body) => s!("do", cond, body),
            Dot(ref obj, ref key) => s!("dot", obj, key),
            If(ref cond, ref iftrue, ref maybeiffalse) => s!("if", cond, iftrue, maybeiffalse),
            Label(ref label, ref body) => s!("label", label, body),
            Name(ref name) => s!("name", name),
            New(ref call) => s!("new", call),
            Num(ref num) => s!("num", num),
            Object(ref keyvals) => s!("object", keyvals),
            Return(ref retval) => s!("return", retval),
            Seq(ref left, ref right) => s!("seq", left, right),
            Stat(ref stat) => s!("stat", stat),
            String(ref string) => s!("string", string),
            Sub(ref target, ref index) => s!("sub", target, index),
            Switch(ref input, ref cases) => s!("switch", input, cases),
            Toplevel(ref stats) => s!("toplevel", stats),
            UnaryPrefix(ref op, ref right) => s!("unary-prefix", op, right),
            Var(ref vars) => s!("var", vars),
            While(ref cond, ref body) => s!("while", cond, body),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    null,
    str(IString),
    num(f64),
    arr(ArrayStorage),
    boo(bool),
    obj(ObjectStorage),
}

impl Eq for Value {}
impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (&Value::null, &Value::null) => true,
            (&Value::num(n1), &Value::num(n2)) => n1 == n2,
            (&Value::str(ref s1), &Value::str(ref s2)) => s1 == s2,
            (&Value::boo(b1), &Value::boo(b2)) => b1 == b2,
            // if you want a deep compare, use deepCompare
            (&Value::arr(_), _) |
            (&Value::obj(_), _) => self as *const _ == other as *const _,
            _ => false,
        }
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        // drop is called when assigning over a value - make sure it's been cleared
        // back to null
        if let Value::null = *self {} else { panic!() }
    }
}

// RSTODO: are the return values needed in set* and assignFrom?
impl Value {
    fn new() -> Value {
        Value::null
    }
    // RSTODO: move this into drop?
    fn free(&mut self) {
        match *self {
            // arrays are in arena, don't drop
            // RSTODO: arrays aren't in arena in rust
            Value::arr(ref mut a) => {
                a.truncate(0);
                a.shrink_to_fit();
            },
            // hashmaps aren't in arena, drop
            Value::obj(ref mut o) => unsafe { ptr::drop_in_place(o as *mut _) },
            // IStrings may be dynamically allocated, so drop
            // RSTODO: may be easier to just leave them around?
            Value::str(ref mut s) => unsafe { ptr::drop_in_place(s as *mut _) },
            Value::null |
            Value::num(_) |
            Value::boo(_) => (),
        }
        // Any drops and memory freeing has been done above
        unsafe { ptr::write(self as *mut _, Value::null) }
    }

    fn from_str(s: &str) -> Value {
        // RSTODO: alloc instead of new?
        let mut v = Value::new();
        v.setString(s);
        v
    }
    fn from_double(n: f64) -> Value {
        // RSTODO: alloc instead of new?
        let mut v = Value::new();
        v.setNumber(n);
        v
    }
    fn from_arraystorage(a: &ArrayStorage) -> Value {
        // RSTODO: alloc instead of new?
        let mut v = Value::new();
        v.setArray(a);
        v
    }

    fn setString(&mut self, s: &str) -> &mut Value {
        self.free();
        *self = Value::str(IString::from(s));
        self
    }
    pub fn setIString(&mut self, a: IString) -> &mut Value {
        self.free();
        *self = Value::str(a);
        self
    }
    fn setNumber(&mut self, n: f64) -> &mut Value {
        self.free();
        *self = Value::num(n);
        self
    }
    fn setArray(&mut self, a: &ArrayStorage) -> &mut Value {
        self.free();
        let mut sa = ARENA.allocArray();
        sa.extend_from_slice(a);
        *self = Value::arr(sa);
        self
    }
    pub fn setArrayHint(&mut self, size_hint: usize) -> &mut Value {
        self.free();
        let mut sa = ARENA.allocArray();
        sa.reserve(size_hint);
        *self = Value::arr(sa);
        self
    }
    fn setNull(&mut self) -> &mut Value {
        self.free();
        *self = Value::null;
        self
    }
    pub fn setBool(&mut self, b: bool) -> &mut Value {
        self.free();
        *self = Value::boo(b);
        self
    }
    fn setObject(&mut self) -> &mut Value {
        self.free();
        *self = Value::obj(ObjectStorage::new());
        self
    }

    pub fn isString(&self) -> bool {
        if let &Value::str(_) = self { true } else { false }
    }
    fn isNumber(&self) -> bool {
        if let &Value::num(_) = self { true } else { false }
    }
    fn isArray(&self) -> bool {
        if let &Value::arr(_) = self { true } else { false }
    }
    fn isNull(&self) -> bool {
        if let &Value::null = self { true } else { false }
    }
    fn isBool(&self) -> bool {
        if let &Value::boo(_) = self { true } else { false }
    }
    fn isObject(&self) -> bool {
        if let &Value::obj(_) = self { true } else { false }
    }

    // RSTODO: is this comment relevant?
    // avoid overloading == as it might overload over int
    fn isBoolEqual(&self, b: bool) -> bool {
        if let &Value::boo(sb) = self { b == sb } else { false }
    }

    pub fn getStr(&self) -> &str {
        if let &Value::str(ref a) = self { &*a } else { panic!() }
    }
    pub fn getIString(&self) -> IString {
        if let &Value::str(ref a) = self { a.clone() } else { panic!() }
    }
    pub fn getNumber(&self) -> f64 {
        if let &Value::num(d) = self { d } else { panic!() }
    }
    fn getBool(&self) -> bool {
        if let &Value::boo(b) = self { b } else { panic!() }
    }
    pub fn getArray(&self) -> &ArrayStorage {
        if let &Value::arr(ref a) = self { a } else { panic!() }
    }
    pub fn getArrayMut(&mut self) -> &mut ArrayStorage {
        if let &mut Value::arr(ref mut a) = self { a } else { panic!() }
    }
    fn getObject(&self) -> &ObjectStorage {
        if let &Value::obj(ref o) = self { o } else { panic!() }
    }
    fn getObjectMut(&mut self) -> &mut ObjectStorage {
        if let &mut Value::obj(ref mut o) = self { o } else { panic!() }
    }

    // convenience function to get a known integer
    pub fn getInteger(&self) -> i64 {
        f64toi64(self.getNumber())
    }

    fn assignFrom(&mut self, other: &Value) -> &Value {
        self.free();
        match *other {
            Value::null => self.setNull(),
            Value::str(ref a) => self.setIString(a.clone()),
            Value::num(d) => self.setNumber(d),
            Value::arr(ref a) => self.setArray(a),
            Value::boo(b) => self.setBool(b),
            Value::obj(_) => panic!(), // TODO
        };
        self
    }

    fn deepCompare(&self, other: Ref) -> bool {
        // either same pointer, or identical value type (str, number, null or bool)
        if self == &*other { return true }
        // https://github.com/rust-lang/rust/issues/24263 - enum discriminant
        let typesame = match *self {
            Value::null => other.isNull(),
            Value::str(_) => other.isString(),
            Value::num(_) => other.isNumber(),
            Value::arr(_) => other.isArray(),
            Value::boo(_) => other.isBool(),
            Value::obj(_) => other.isObject(),
        };
        if !typesame { return false }
        if self.isArray() {
            let (arr1, arr2) = (self.getArray(), other.getArray());
            if arr1.len() != arr2.len() { return false }
            arr1.iter().zip(arr2).all(|(v1, &v2)| v1.deepCompare(v2))
        } else if self.isObject() {
            let (obj1, obj2) = (self.getObject(), other.getObject());
            if obj1.len() != obj2.len() { return false }
            obj1.iter().all(|(k, v1)|
                if let Some(&v2) = obj2.get(k) { v1.deepCompare(v2) } else { false }
            )
        } else {
            false
        }
    }

    pub fn parse(&mut self, curr: &[u8]) {
        let json: serde_json::Value = serde_json::from_slice(curr).unwrap();
        self.parse_json(&json);
    }
    fn parse_json(&mut self, json: &serde_json::Value) {
        match *json {
            serde_json::Value::Null => self.setNull(),
            serde_json::Value::Bool(b) => self.setBool(b),
            serde_json::Value::I64(n) => self.setNumber(n as f64),
            serde_json::Value::U64(n) => self.setNumber(n as f64),
            serde_json::Value::F64(n) => self.setNumber(n),
            serde_json::Value::String(ref s) => self.setString(s),
            serde_json::Value::Array(ref a) => {
                self.setArrayHint(a.len());
                let iter = a.iter().map(|v| {
                    let mut r = ARENA.alloc(); r.parse_json(v); r
                });
                match *self {
                    Value::arr(ref mut sa) => sa.extend(iter),
                    _ => unreachable!(),
                };
                self
            },
            serde_json::Value::Object(ref o) => {
                self.setObject();
                self.getObjectMut().extend(o.into_iter().map(|(key, val)| {
                    let mut r = ARENA.alloc();
                    r.parse_json(val);
                    (IString::from(key.as_str()), r)
                }));
                self
            },
        };
    }

    pub fn stringify<T>(&self, out: &mut T, pretty: bool) where T: Write {
        let jsonobj = self.stringify_json();
        let outstr = if pretty {
            serde_json::ser::to_string_pretty(&jsonobj)
        } else {
            serde_json::ser::to_string(&jsonobj)
        }.unwrap();
        out.write(outstr.as_bytes()).unwrap();
    }
    fn stringify_json(&self) -> serde_json::Value {
        match *self {
            Value::null => serde_json::Value::Null,
            Value::str(ref a) => serde_json::Value::String((&**a).to_string()),
            // RSTODO: C++ float serialization is different to serde
            Value::num(n) => serde_json::Value::F64(n),
            Value::boo(b) => serde_json::Value::Bool(b),
            Value::arr(ref a) => {
                let outvec = a.iter().map(|v| v.stringify_json()).collect();
                serde_json::Value::Array(outvec)
            },
            Value::obj(ref o) => {
                let outmap = o.iter().map(
                    |(k, v)| ((&**k).to_string(), v.stringify_json())
                ).collect();
                serde_json::Value::Object(outmap)
            },
        }
    }

    // String operations

    // Number operations

    // Array operations

    pub fn size(&self) -> usize {
        self.getArray().len()
    }

    fn setSize(&mut self, size: usize) {
        let a = self.getArrayMut();
        let old = a.len();
        if old < size {
            a.reserve_exact(size - old);
        }
        for _ in old..size {
            a.push(ARENA.alloc());
        }
    }

    pub fn get(&self, x: usize) -> Ref {
        *self.getArray().get(x).unwrap()
    }

    fn push_back(&mut self, r: Ref) -> &mut Value {
        self.getArrayMut().push(r);
        self
    }

    fn pop_back(&mut self) -> Ref {
        self.getArrayMut().pop().unwrap()
    }

    fn back(&self) -> Option<Ref> {
        self.getArray().last().cloned()
    }

    fn splice(&mut self, x: usize, num: usize) {
        self.getArrayMut().splice(x..x+num, iter::empty());
    }

    // RSTODO: https://github.com/rust-lang/rfcs/issues/1065
    // RSTODO: should this be implemented on vec instead? See other uses of
    // slice in the optimizer
    fn insertEmpties(&mut self, x: usize, num: usize) {
        let empties: Vec<_> = iter::repeat(EMPTYREF).take(num).collect();
        self.getArrayMut().splice(x..x, empties.into_iter());
    }

    fn insert(&mut self, x: usize, node: Ref) {
        self.getArrayMut().insert(x, node);
    }

    fn indexOf(&self, other: Ref) -> isize {
        match self.getArray().iter().position(|&r| *r == *other) {
            Some(i) => i as isize,
            None => -1,
        }
    }

    fn map<F>(&self, func: F) -> Ref where F: Fn(Ref) -> Ref {
        let a = self.getArray();
        let mut ret = ARENA.alloc();
        ret.setArrayHint(a.len());
        {
            let mut retarr = ret.getArrayMut();
            for r in a {
                retarr.push(func(r.clone()));
            }
        }
        ret
    }

    fn filter<F>(&self, func: F) -> Ref where F: Fn(Ref) -> bool {
        let a = self.getArray();
        let mut ret = ARENA.alloc();
        ret.setArrayHint(0);
        {
            let mut retarr = ret.getArrayMut();
            for r in a {
                if func(r.clone()) { retarr.push(r.clone()) }
            }
        }
        ret
    }

    // Null operations

    // Bool operations

    // Object operations

    fn lookup(&mut self, x: IString) -> Ref {
        self.getObjectMut().entry(x).or_insert(EMPTYREF).clone()
    }

    fn has(&self, x: IString) -> bool {
        self.getObject().contains_key(&x)
    }
}

// AST traversals

// Traversals

struct TraverseInfo {
  node: Ref,
  index: isize,
  arrlen: isize,
  arrdata: *const Ref,
}

impl TraverseInfo {
    fn new(node: Ref, len: isize, data: *const Ref) -> TraverseInfo {
        TraverseInfo { node: node, index: 0, arrlen: len, arrdata: data }
    }
}

// RSTODO: originally 40, but rust isn't generic over integer params and 40
// isn't explicitly implemented in smallvec
const TRAV_STACK: usize = 32;

struct StackedStack<T> { // a stack, on the stack
    // smallvec automatically handles spilling
    storage: SmallVec<[T; TRAV_STACK]>,
}

impl<T> StackedStack<T> {
    fn new() -> StackedStack<T> {
        StackedStack {
            storage: SmallVec::new(),
        }
    }

    fn len(&self) -> usize {
        self.storage.len()
    }

    fn push_back(&mut self, t: T) {
        self.storage.push(t)
    }

    fn back(&mut self) -> &mut T {
        let len = self.storage.len();
        assert!(len > 0);
        unsafe { self.storage.get_unchecked_mut(len-1) }
    }

    fn pop_back(&mut self) {
        self.storage.pop().unwrap();
    }
}

// RSTODO: https://github.com/rust-lang/rfcs/issues/372 would make this code nicer

// Traverse, calling visit before the children
pub fn traversePre<F>(node: &mut AstValue, mut visit: F) where F: FnMut(&mut AstValue) {
    type It<'a> = Box<Iterator<Item=&'a mut AstNode>>;
    visit(node);
    let mut stack = StackedStack::new();
    stack.push_back(node.children::<It>());
    loop {
        if let Some(node) = stack.back().next() {
            visit(node);
            stack.push_back(node.children::<It>());
        } else {
            stack.pop_back();
            if stack.len() == 0 { break }
        }
    }
}

// Traverse, calling visitPre before the children and visitPost after
pub fn traversePrePost<F1,F2>(node: &mut AstValue, mut visitPre: F1, mut visitPost: F2) where F1: FnMut(&mut AstValue), F2: FnMut(&mut AstValue) {
    type It<'a> = Box<Iterator<Item=&'a mut AstNode>>;
    visitPre(node);
    let mut stack = StackedStack::new();
    stack.push_back((node as *mut _, node.children::<It>()));
    loop {
        if let Some(&mut box ref mut node) = stack.back().1.next() {
            visitPre(node);
            stack.push_back((node as *mut _, node.children::<It>()));
        } else {
            visitPost(unsafe { &mut *stack.back().0 });
            stack.pop_back();
            if stack.len() == 0 { break }
        }
    }
}

// Traverse, calling visitPre before the children and visitPost after. If pre returns false, do not traverse children
fn traversePrePostConditional<F1,F2>(node: &mut AstValue, mut visitPre: F1, mut visitPost: F2) where F1: FnMut(&mut AstValue) -> bool, F2: FnMut(&mut AstValue) {
    type It<'a> = Box<Iterator<Item=&'a mut AstNode>>;
    if !visitPre(node) { return };
    let mut stack = StackedStack::new();
    stack.push_back((node as *mut _, node.children::<It>()));
    loop {
        if let Some(&mut box ref mut node) = stack.back().1.next() {
            if !visitPre(node) { continue };
            stack.push_back((node as *mut _, node.children::<It>()));
        } else {
            visitPost(unsafe { &mut *stack.back().0 });
            stack.pop_back();
            if stack.len() == 0 { break }
        }
    }
}

pub fn traverseFunctions<F>(ast: &mut AstValue, mut visit: F) where F: FnMut(&mut AstValue) {
    match *ast {
        Toplevel(ref mut stats) => {
            for curr in stats.iter_mut() {
                if let Defun(..) = **curr { visit(curr) }
            }
        },
        Defun(..) => visit(ast),
        _ => {},
    }
}

pub fn dump(s: &str, node: Ref, pretty: bool) {
    let mut stderr = io::stderr();
    write!(stderr, "{}: ", s).unwrap();
    if node.is_something() { node.stringify(&mut stderr, pretty); }
    else { stderr.write(b"(nullptr)").unwrap(); }
    stderr.write(b"\n").unwrap();
}

pub fn printAst(pretty: bool, finalize: bool, ast: &AstValue) -> Vec<u8> {
    let mut jsp = JSPrinter::new(pretty, finalize, ast);
    jsp.printAst();
    jsp.buffer
}

struct JSPrinter<'a> {
    pretty: bool,
    finalize: bool,

    buffer: Vec<u8>,

    indent: usize,
    possibleSpace: bool, // add a space to separate identifiers

    ast: &'a AstValue,
}

impl<'a> JSPrinter<'a> {
    fn new(pretty: bool, finalize: bool, ast: &AstValue) -> JSPrinter {
        JSPrinter {
            pretty: pretty,
            finalize: finalize,
            buffer: vec![],
            indent: 0,
            possibleSpace: false,
            ast: ast,
        }
    }

    fn printAst(&mut self) {
        self.print(self.ast);
    }

    // Utils

    fn emit(&mut self, c: u8) {
        self.maybeSpace(c);
        // optimize ;} into }, the ; is not separating anything
        if !self.pretty && c == b'}' && *self.buffer.last().unwrap() == b';' {
            self.buffer.pop().unwrap();
        }
        self.buffer.push(c);
    }

    fn emitBuf(&mut self, cs: &[u8]) {
        self.maybeSpace(cs[0]);
        self.buffer.extend_from_slice(cs);
    }

    fn newline(&mut self) {
        if !self.pretty { return }
        self.emit(b'\n');
        for _ in 0..self.indent { self.emit(b' ') }
    }

    fn space(&mut self) {
        if self.pretty { self.emit(b' ') }
    }

    fn safeSpace(&mut self) {
        if self.pretty { self.emit(b' ') } else { self.possibleSpace = true }
    }

    fn maybeSpace(&mut self, s: u8) {
        if self.possibleSpace {
            self.possibleSpace = false;
            if isIdentPart(s) { self.emit(b' ') }
        }
    }

    fn print(&mut self, node: &AstValue) {
        self.buffer.reserve(100);
        //fprintf(stderr, "printing %s\n", type.str);
        match *node {
            Array(ref nodes) => {
                self.emit(b'[');
                let mut first = true;
                for node in nodes.iter() {
                    if !first {
                        if self.pretty { self.emitBuf(b", ") } else { self.emit(b',') }
                    }
                    self.print(node);
                    first = false
                }
                self.emit(b']')
            },
            Assign(_, ref left, ref right) => {
                self.printChild(left, node, -1);
                self.space();
                self.emit(b'=');
                self.space();
                self.printChild(right, node, 1)
            },
            Binary(ref op, ref left, ref right) => {
                self.printChild(left, node, -1);
                self.space();
                self.emitBuf(op.as_bytes());
                self.space();
                self.printChild(right, node, 1)
            },
            Block(ref stats) => {
                if stats.is_empty() {
                    self.emitBuf(b"{}");
                    return
                }
                self.emit(b'{');
                self.indent += 1;
                self.newline();
                self.printStats(stats);
                self.indent -= 1;
                self.newline();
                self.emit(b'}')
            },
            Break(ref label) => {
                self.emitBuf(b"break");
                if let Some(ref s) = *label {
                    self.emit(b' ');
                    self.emitBuf(s.as_bytes())
                }
                self.emit(b';')
            },
            Call(ref fnexpr, ref params) => {
                self.printChild(fnexpr, node, 0);
                self.emit(b'(');
                let mut first = true;
                for param in params.iter() {
                    if !first {
                        if self.pretty { self.emitBuf(b", ") } else { self.emit(b',') }
                    }
                    self.printChild(param, node, 0);
                    first = false
                }
                self.emit(b')')
            },
            Conditional(ref cond, ref iftrue, ref iffalse) => {
                self.printChild(cond, node, -1);
                self.space();
                self.emit(b'?');
                self.space();
                self.printChild(iftrue, node, 0);
                self.space();
                self.emit(b':');
                self.space();
                self.printChild(iffalse, node, 1);
            },
            Continue(ref label) => {
                self.emitBuf(b"continue");
                if let Some(ref s) = *label {
                    self.emit(b' ');
                    self.emitBuf(s.as_bytes())
                }
                self.emit(b';')
            },
            Defun(ref fname, ref args, ref stats) => {
                self.emitBuf(b"function ");
                self.emitBuf(fname.as_bytes());
                self.emit(b'(');
                let mut first = true;
                for arg in args.iter() {
                    if !first {
                        if self.pretty { self.emitBuf(b", ") } else { self.emit(b',') }
                    }
                    self.emitBuf(arg.as_bytes());
                    first = false
                }
                self.emit(b')');
                self.space();
                if stats.is_empty() {
                    self.emitBuf(b"{}");
                    return
                }
                self.emit(b'{');
                self.indent += 1;
                self.newline();
                self.printStats(stats);
                self.indent -= 1;
                self.newline();
                self.emit(b'}');
                self.newline();
            },
            Do(ref cond, ref body) => {
                self.emitBuf(b"do");
                self.safeSpace();
                self.printOtherwise(body, b"{}");
                self.space();
                self.emitBuf(b"while");
                self.space();
                self.emit(b'(');
                self.print(cond);
                self.emit(b')');
                self.emit(b';');
            },
            Dot(ref obj, ref key) => {
                self.print(obj);
                self.emit(b'.');
                self.emitBuf(key.as_bytes())
            },
            If(ref cond, ref iftrue, ref maybeiffalse) => {
                fn ifHasElse(node: &AstValue) -> bool { node.getIf().2.is_some() }
                self.emitBuf(b"if");
                self.safeSpace();
                self.emit(b'(');
                self.print(cond);
                self.emit(b')');
                self.space();
                // special case: we need braces to save us from ambiguity, if () { if () } else. otherwise else binds to inner if
                // also need to recurse for                                if () { if () { } else { if () } else
                // (note that this is only a problem if the if body has a single element in it, not a block or such, as then
                // the block would be braced)
                // this analysis is a little conservative - it assumes any child if could be confused with us, which implies
                // all other braces vanished (the worst case for us, we are not saved by other braces).
                let mut needBraces = false;
                // RSTODO: convince myself this dance is necessary
                if ifHasElse(node){
                    let mut child = iftrue;
                    while let If(_, _, ref maybeiffalse) = **child {
                        if let Some(ref iffalse) = *maybeiffalse {
                            child = iffalse // continue into the else
                        } else {
                            needBraces = true;
                            break
                        }
                    }
                }
                if needBraces {
                    self.emit(b'{');
                    self.indent += 1;
                    self.newline();
                    self.print(iftrue);
                    self.indent -= 1;
                    self.newline();
                    self.emit(b'}')
                } else {
                    self.printOtherwise(iftrue, b"{}")
                }
                if let Some(ref iffalse) = *maybeiffalse {
                    self.space();
                    self.emitBuf(b"else");
                    self.safeSpace();
                    self.printOtherwise(iffalse, b"{}")
                }
            },
            Label(ref label, ref body) => {
                self.emitBuf(label.as_bytes());
                self.space();
                self.emit(b':');
                self.space();
                self.print(body)
            },
            Name(ref name) => {
                self.emitBuf(name.as_bytes())
            },
            New(ref call) => {
                self.emitBuf(b"new ");
                self.print(call)
            },
            Num(num) => {
                let finalize = self.finalize;
                self.emitBuf(&Self::numToString(num, finalize))
            },
            Object(ref keyvals) => {
                self.emit(b'{');
                self.indent += 1;
                self.newline();
                let mut first = true;
                for &(ref key, ref val) in keyvals.iter() {
                    if !first {
                        if self.pretty { self.emitBuf(b", ") } else { self.emit(b',') }
                        self.newline();
                    }
                    self.emit(b'"');
                    self.emitBuf(key.as_bytes());
                    self.emitBuf(b"\":");
                    self.space();
                    self.print(val);
                    first = false
                }
                self.indent -= 1;
                self.newline();
                self.emit(b'}')
            },
            Return(ref retval) => {
                self.emitBuf(b"return");
                if let Some(ref r) = *retval {
                    self.emit(b' ');
                    self.print(r)
                }
                self.emit(b';')
            },
            Seq(ref left, ref right) => {
                self.printChild(left, node, -1);
                self.emit(b',');
                self.space();
                self.printChild(right, node, 1)
            },
            Stat(ref stat) => {
                if Self::isNothing(stat) { return }
                self.print(stat);
                if *self.buffer.last().unwrap() != b';' { self.emit(b';') }
            },
            String(ref string) => {
                self.emit(b'"');
                self.emitBuf(string.as_bytes());
                self.emit(b'"')
            },
            Sub(ref target, ref index) => {
                self.printChild(target, node, -1);
                self.emit(b'[');
                self.print(index);
                self.emit(b']')
            },
            Switch(ref input, ref cases) => {
                self.emitBuf(b"switch");
                self.space();
                self.emit(b'(');
                self.print(input);
                self.emit(b')');
                self.space();
                self.emit(b'{');
                self.newline();
                for &(ref case, ref stats) in cases.iter() {
                    if let Some(ref c) = *case {
                        self.emitBuf(b"case ");
                        self.print(c);
                        self.emit(b':')
                    } else {
                        self.emitBuf(b"default:")
                    }
                    if stats.is_empty() {
                        self.newline()
                    } else {
                        self.indent += 1;
                        self.newline();
                        let curr = self.buffer.len();
                        self.printStats(stats);
                        self.indent -= 1;
                        if curr != self.buffer.len() {
                            self.newline()
                        } else {
                            self.buffer.pop().unwrap(); // avoid the extra indentation we added tentatively
                        }
                    }
                }
                self.emit(b'}')
            },
            Toplevel(ref stats) => {
                if !stats.is_empty() { self.printStats(stats) }
            },
            UnaryPrefix(ref op, ref right) => {
                // RSTODO: ideally this would use && https://github.com/rust-lang/rfcs/issues/929
                let matches = if let mast!(UnaryPrefix(is!("-"), Num(_))) = *right { true } else { right.isNum() };
                if self.finalize && *op == is!("+") && matches {
                    // emit a finalized number
                    let last = self.buffer.len();
                    self.print(right);
                    if self.buffer[last..].iter().position(|&b| b == b'.').is_some() {
                        return // already a decimal point, all good
                    }
                    let e = if let Some(e) = self.buffer[last..].iter().position(|&b| b == b'e') {
                        e
                    } else {
                        // RSTODO: why not just emit '.'?
                        self.emitBuf(b".0");
                        return
                    };
                    self.buffer.splice(last+e..last+e, vec![b'.', b'0']);
                    return
                }
                let lastchr = *self.buffer.last().unwrap();
                if (lastchr == b'-' && *op == is!("-")) || (lastchr == b'+' && *op == is!("+")) {
                    self.emit(b' ')
                }
                self.emitBuf(op.as_bytes());
                self.printChild(right, node, 1)
            },
            Var(ref vars) => {
                self.emitBuf(b"var ");
                let mut first = true;
                for &(ref name, ref val) in vars.iter() {
                    if !first {
                        if self.pretty { self.emitBuf(b", ") } else { self.emit(b',') }
                    }
                    self.emitBuf(name.as_bytes());
                    if let Some(ref val) = *val {
                        self.space();
                        self.emit(b'=');
                        self.space();
                        self.print(val)
                    }
                    first = false
                }
                self.emit(b';');
            },
            While(ref cond, ref body) => {
                self.emitBuf(b"while");
                self.space();
                self.emit(b'(');
                self.print(cond);
                self.emit(b')');
                self.space();
                self.printOtherwise(body, b"{}")
            },
        }
    }

    // print a node, and if nothing is emitted, emit something instead
    fn printOtherwise(&mut self, node: &AstValue, otherwise: &[u8]) {
        let last = self.buffer.len();
        self.print(node);
        if self.buffer.len() == last { self.emitBuf(otherwise) }
    }

    fn printStats(&mut self, stats: &[AstNode]) {
        let mut first = true;
        for stat in stats {
            if Self::isNothing(stat) { continue }
            if first { first = false } else { self.newline() }
            self.print(stat)
        }
    }

    fn isNothing(node: &AstValue) -> bool {
        match *node {
            Toplevel(ref stats) if stats.is_empty() => true,
            Stat(ref stat) if Self::isNothing(stat) => true,
            _ => false,
        }
    }

    fn numToString(mut d: f64, finalize: bool) -> Vec<u8> {
        let neg = d < 0f64;
        if neg { d = -d }
        // try to emit the fewest necessary characters
        let integer = isInteger(d);
        // f is normal, e is scientific for float, x for integer
        let BUFFERSIZE: usize = 1000;
        let mut storage_f = Vec::with_capacity(BUFFERSIZE);
        let mut storage_e = Vec::with_capacity(BUFFERSIZE);
        let mut err_f = 0f64;
        let mut err_e = 0f64;
        for &e in &[false, true] {
            let buffer = if e { &mut storage_e } else { &mut storage_f };
            let temp: f64 = if !integer {
                let mut cur = 0f64;
                for i in 0..19 {
                    buffer.clear();
                    if e { write!(buffer, "{:.*e}", i, d) } else { write!(buffer, "{:.*}", i, d) }.unwrap();
                    cur = str::from_utf8(buffer).unwrap().parse().unwrap();
                    if cur == d { break }
                }
                cur
            } else {
                assert!(d >= 0f64);
                if isInteger64(d) {
                    let asHex = e && !finalize;
                    if asHex {
                        write!(buffer, "{:#x}", f64tou64(d)).unwrap();
                        u64::from_str_radix(str::from_utf8(&buffer[2..]).unwrap(), 16).unwrap() as f64
                    } else {
                        write!(buffer, "{}", d as u64).unwrap();
                        str::from_utf8(buffer).unwrap().parse().unwrap()
                    }
                } else {
                    // too large for a machine integer, just use floats
                    if e { write!(buffer, "{:.6e}", d) } else { write!(buffer, "{:}", d) }.unwrap(); // even on integers, e with a dot is useful, e.g. 1.2e+200
                    str::from_utf8(buffer).unwrap().parse().unwrap()
                }
                //errv("%.18f, %.18e   =>   %s   =>   %.18f, %.18e, %llu   (%d)\n", d, d, buffer, temp, temp, uu, temp == d);
            };
            if e { err_e = (temp - d).abs() } else { err_f = (temp -d).abs() }
            //errv("current attempt: %.18f  =>  %s", d, buffer);
            //assert(temp == d);
            let maybedot = buffer.iter().position(|&b| b == b'.');
            if let Some(dot) = maybedot {
                // remove trailing zeros
                let mut end = dot + 1;
                while end < buffer.len() {
                    let ch = buffer[end];
                    if ch < b'0' || ch > b'9' { break }
                    end += 1
                }
                end -= 1;
                while buffer[end] == b'0' {
                    buffer.remove(end);
                    end -= 1
                }
                //errv("%.18f  =>   %s", d, buffer);
                // remove preceding zeros
                while buffer[0] == b'0' {
                    buffer.remove(0);
                }
                //errv("%.18f ===>  %s", d, buffer);
            } else if !integer || !e {
                // no dot. try to change 12345000 => 12345e3
                let mut end = buffer.len();
                end -= 1;
                let mut test = end;
                // remove zeros, and also doubles can use at most 24 digits, we can truncate any extras even if not zero
                while (buffer[test] == b'0' || test > 24) && test > 0 { test -= 1 }
                let num = end - test;
                if num >= 3 {
                    test += 1;
                    buffer.truncate(test);
                    buffer.push(b'e');
                    if num < 10 {
                        buffer.extend_from_slice(&[b'0' + num as u8])
                    } else if num < 100 {
                        buffer.extend_from_slice(&[b'0' + num.checked_div(10).unwrap() as u8, b'0' + (num % 10) as u8])
                    } else {
                        assert!(num < 1000);
                        buffer.extend_from_slice(&[b'0' + num.checked_div(100).unwrap() as u8, b'0' + (num % 100).checked_div(10).unwrap() as u8, b'0' + (num % 10) as u8])
                    }
                }
            }
            //errv("..current attempt: %.18f  =>  %s", d, buffer);
        }
        //fprintf(stderr, "options:\n%s\n%s\n (first? %d)\n", storage_e, storage_f, strlen(storage_e) < strlen(storage_f));
        let mut ret = if err_e == err_f {
            if storage_e.len() < storage_f.len() { storage_e } else { storage_f }
        } else {
            if err_e < err_f { storage_e } else { storage_f }
        };
        if neg {
            // RSTODO: probably a way to do this function without inserting
            ret.insert(0, b'-');
        }
        ret
    }

    // Parens optimizing

// RSTODO: remove?
//  bool capturesOperators(Ref node) {
//    Ref type = node[0];
//    return type == CALL || type == ARRAY || type == OBJECT || type == SEQ;
//  }

    fn getPrecedence(node: &AstValue, parent: bool) -> isize {
        let ret = match *node {
            Binary(ref op, _, _) |
            UnaryPrefix(ref op, _) => OpClass::getPrecedence(if node.isBinary() { OpClassTy::Binary } else { OpClassTy::Prefix }, op.clone()),
            Seq(..) => OpClass::getPrecedence(OpClassTy::Binary, is!(",")),
            // call arguments are split by commas, but call itself is safe
            Call(..) => if parent { OpClass::getPrecedence(OpClassTy::Binary, is!(",")) } else { return -1 },
            Assign(..) => OpClass::getPrecedence(OpClassTy::Binary, is!("=")),
            Conditional(..) => OpClass::getPrecedence(OpClassTy::Tertiary, is!("?")),
            // otherwise, this is something that fixes precedence explicitly, and we can ignore
            _ => return -1, // XXX
        };
        assert!(ret < isize::MAX as usize);
        ret as isize
    }

    // check whether we need parens for the child, when rendered in the parent
    // @param childPosition -1 means it is printed to the left of parent, 0 means "anywhere", 1 means right
    fn needParens(parent: &AstValue, child: &AstValue, childPosition: isize) -> bool {
        let parentPrecedence = Self::getPrecedence(parent, true);
        let childPrecedence = Self::getPrecedence(child, false);

        if childPrecedence > parentPrecedence { return true }  // child is definitely a danger
        if childPrecedence < parentPrecedence { return false } //          definitely cool
        // equal precedence, so associativity (rtl/ltr) is what matters
        // (except for some exceptions, where multiple operators can combine into confusion)
        if let UnaryPrefix(ref op, _) = *parent {
            let (childop, _) = child.getUnaryPrefix();
            if (*op == is!("+") || *op == is!("-")) && childop == op {
                // cannot emit ++x when we mean +(+x)
                return true
            }
        }
        if childPosition == 0 { return true } // child could be anywhere, so always paren
        if childPrecedence < 0 { return false } // both precedences are safe
        // check if child is on the dangerous side
        // RSTODO: valid assertion?
        assert!(parentPrecedence > -1);
        if OpClass::getRtl(parentPrecedence as usize) { return childPosition < 0 }
        childPosition > 0
    }

    fn printChild(&mut self, child: &AstValue, parent: &AstValue, childPosition: isize) {
        let parens = Self::needParens(parent, child, childPosition);
        if parens { self.emit(b'(') }
        self.print(child);
        if parens { self.emit(b')') }
    }
}

// cashew builder
pub mod builder {

    use super::super::IString;
    use super::{AstNode, AstValue, AstVec};
    use super::AstValue::*;

    fn is_statable(av: &AstValue) -> bool {
        match *av {
            Assign(..) |
            Call(..) |
            Binary(..) |
            UnaryPrefix(..) |
            If(..) |
            Name(..) |
            Num(..) |
            Conditional(..) |
            Dot(..) |
            New(..) |
            Sub(..) |
            Seq(..) |
            String(..) |
            Object(..) |
            Array(..) => true,
            _ => false,
        }
    }

    pub fn makeTArray<T>(size_hint: usize) -> AstVec<T> {
        Box::new(Vec::with_capacity(size_hint))
    }
    pub fn makeRawArray(size_hint: usize) -> AstVec<AstNode> {
        makeTArray(size_hint)
    }

    pub fn makeToplevel() -> AstNode {
        an!(Toplevel(makeRawArray(0)))
    }

    pub fn makeString(s: IString) -> AstNode {
        an!(String(s))
    }

    pub fn makeBlock() -> AstNode {
        an!(Block(makeRawArray(0)))
    }

    pub fn makeName(name: IString) -> AstNode {
        an!(Name(name))
    }

    pub fn setBlockContent(target: &mut AstValue, block: AstNode) {
        let (stats,) = block.intoBlock();
        match *target {
            Toplevel(ref mut s) => *s = stats,
            Defun(_, _, ref mut s) => *s = stats,
            _ => panic!(),
        };
    }

    pub fn appendToBlock(block: &mut AstValue, element: AstNode) {
        let (stats,) = block.getMutBlock();
        stats.push(element);
    }

    pub fn makeCall(target: AstNode) -> AstNode {
        an!(Call(target, makeRawArray(0)))
    }

    pub fn appendToCall(call: &mut AstValue, element: AstNode) {
        let (_, params) = call.getMutCall();
        params.push(element);
    }

    pub fn makeStatement(contents: AstNode) -> AstNode {
        if is_statable(&contents) {
            an!(Stat(contents))
        } else {
            contents // only very specific things actually need to be stat'ed
        }
    }

    pub fn makeDouble(num: f64) -> AstNode {
        an!(Num(num))
    }

    pub fn makeInt(num: u32) -> AstNode {
        makeDouble(num as f64)
    }

    pub fn makeBinary(left: AstNode, op: IString, right: AstNode) -> AstNode {
        match op {
            is!("=") => an!(Assign(true, left, right)),
            is!(",") => an!(Seq(left, right)),
            _ => an!(Binary(op, left, right)),
        }
    }

    pub fn makePrefix(op: IString, right: AstNode) -> AstNode {
        an!(UnaryPrefix(op, right))
    }

    pub fn makeFunction(name: IString) -> AstNode {
        an!(Defun(name, makeTArray(0), makeRawArray(0)))
    }

    // RSTODO: this should fail AIDAN
    pub fn appendArgumentToFunction(func: &mut AstValue, arg: IString) {
        let (_, params, _) = func.getMutDefun();
        params.push(arg);
    }

    // RSTODO: remove is_const?
    pub fn makeVar(_is_const: bool) -> AstNode {
        an!(Var(makeTArray(0)))
    }

    pub fn appendToVar(var: &mut AstValue, name: IString, maybe_value: Option<AstNode>) {
        let (vars,) = var.getMutVar();
        vars.push((name, maybe_value));
    }

    pub fn makeReturn(value: Option<AstNode>) -> AstNode {
        an!(Return(value))
    }

    pub fn makeIndexing(target: AstNode, index: AstNode) -> AstNode {
        an!(Sub(target, index))
    }

    pub fn makeIf(condition: AstNode, ifTrue: AstNode, ifFalse: Option<AstNode>) -> AstNode {
        an!(If(condition, ifTrue, ifFalse))
    }

    pub fn makeConditional(condition: AstNode, ifTrue: AstNode, ifFalse: AstNode) -> AstNode {
        an!(Conditional(condition, ifTrue, ifFalse))
    }

    pub fn makeDo(body: AstNode, condition: AstNode) -> AstNode {
        an!(Do(condition, body))
    }

    pub fn makeWhile(condition: AstNode, body: AstNode) -> AstNode {
        an!(While(condition, body))
    }

    pub fn makeBreak(label: Option<IString>) -> AstNode {
        an!(Break(label))
    }

    pub fn makeContinue(label: Option<IString>) -> AstNode {
        an!(Continue(label))
    }

    pub fn makeLabel(name: IString, body: AstNode) -> AstNode {
        an!(Label(name, body))
    }

    pub fn makeSwitch(input: AstNode) -> AstNode {
        an!(Switch(input, makeTArray(0)))
    }

    pub fn appendCaseToSwitch(switch: &mut AstValue, arg: AstNode) {
        let (_, cases) = switch.getMutSwitch();
        cases.push((Some(arg), *makeRawArray(0)));
    }

    pub fn appendDefaultToSwitch(switch: &mut AstValue) {
        let (_, cases) = switch.getMutSwitch();
        cases.push((None, *makeRawArray(0)));
    }

    pub fn appendCodeToSwitch(switch: &mut AstValue, code: AstNode, explicitBlock: bool) {
        let (_, cases) = switch.getMutSwitch();
        let &mut (_, ref mut switchtarget) = cases.last_mut().unwrap();
        if !explicitBlock {
            let (codesrc,) = code.intoBlock();
            for codepart in *codesrc {
                switchtarget.push(codepart);
            }
        } else {
            assert!(code.isBlock());
            switchtarget.push(code);
        }
    }

    pub fn makeDot(obj: AstNode, key: IString) -> AstNode {
        an!(Dot(obj, key))
    }

    pub fn makeDotAstNode(obj: AstNode, key: AstNode) -> AstNode {
        let (keystr,) = key.intoName();
        makeDot(obj, keystr)
    }

    pub fn makeNew(call: AstNode) -> AstNode {
        an!(New(call))
    }

    pub fn makeArray() -> AstNode {
        an!(Array(makeRawArray(0)))
    }

    pub fn appendToArray(array: &mut AstValue, element: AstNode) {
        let (arr,) = array.getMutArray();
        arr.push(element);
    }

    pub fn makeObject() -> AstNode {
        an!(Object(makeTArray(0)))
    }

    pub fn appendToObject(object: &mut AstValue, key: IString, value: AstNode) {
        let (obj,) = object.getMutObject();
        obj.push((key, value));
    }
}
