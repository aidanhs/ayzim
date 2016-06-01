use std::collections::HashMap;
use std::io::Write;
use std::io;
use std::iter;
use std::ptr;
use std::ops::{Deref, DerefMut};

use odds::vec::VecExt;
use serde;
use serde_json;
use smallvec::SmallVec;
use typed_arena;

use super::IString;
use super::num::f64toi64;

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
        #[derive(Debug)]
        pub enum AstValue {
            $(
                $x($( $y ),*),
            )*
        }
        impl AstValue {
            $( interpolate_idents!{
                pub fn [is $x](&self) -> bool {
                    use self::AstValue::$x;
                    if let $x(..) = *self { true } else { false }
                }
                fn [into $x](self) -> ($( $y ),*,) {
                    use self::AstValue::$x;
                    __ifletify!{ (self) $x($( $y ),+) }
                }
                pub fn [get $x](&self) -> ($( &$y ),*,) {
                    use self::AstValue::$x;
                    __ifletify!{ ref (*self) $x($( $y ),+) }
                }
                pub fn [getMut $x](&mut self) -> ($( &mut $y ),*,) {
                    use self::AstValue::$x;
                    __ifletify!{ mut (*self) $x($( $y ),+) }
                }
            } )*
        }
    }
}

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
        use self::AstValue::*;
        let refarr = inref.getArray();
        Box::new(match (refarr[0].getIString(), &refarr[1..]) {
            (is!("array"), [arr]) => Array(b(mkarr(arr))),
            (is!("assign"), [b, left, right]) => Assign(b.getBool(), p(left), p(right)),
            (is!("binary"), [op, left, right]) => Binary(op.getIString(), p(left), p(right)),
            (is!("block"), [stats]) => Block(b(mkarr(stats))),
            (is!("break"), [label]) => Break(mklabel(label)),
            (is!("call"), [fnexpr, params]) => Call(p(fnexpr), b(mkarr(params))),
            (is!("conditional"), [cond, iftrue, iffalse]) => Conditional(p(cond), p(iftrue), p(iffalse)),
            (is!("continue"), [label]) => Continue(mklabel(label)),
            (is!("defun"), [fnname, params, stats]) => Defun(fnname.getIString(), b(params.getArray().iter().map(|r| r.getIString()).collect()), b(mkarr(stats))),
            (is!("do"), [cond, body]) => Do(p(cond), p(body)),
            (is!("dot"), [obj, key]) => Dot(p(obj), key.getIString()),
            (is!("if"), [cond, iftrue, iffalse]) => If(p(cond), p(iftrue), maybe_parse(iffalse)),
            (is!("label"), [label, body]) => Label(label.getIString(), p(body)),
            (is!("name"), [name]) => Name(name.getIString()),
            (is!("new"), [call]) => New(p(call)),
            (is!("num"), [num]) => Num(num.getNumber()),
            (is!("object"), [keyvals]) => Object(b(keyvals.getArray().iter().map(|kv| { (kv.get(0).getIString(), p(kv.get(1))) }).collect())),
            (is!("return"), [retval]) => Return(maybe_parse(retval)),
            (is!("seq"), [left, right]) => Seq(p(left), p(right)),
            (is!("stat"), [stat]) => Stat(p(stat)),
            (is!("string"), [string]) => String(string.getIString()),
            (is!("sub"), [target, index]) => Sub(p(target), p(index)),
            (is!("switch"), [input, cases]) => Switch(p(input), b(cases.getArray().iter().map(|casedef| { (maybe_parse(casedef.get(0)), mkarr(casedef.get(1))) }).collect())),
            (is!("toplevel"), [stats]) => Toplevel(b(mkarr(stats))),
            (is!("unary-prefix"), [op, right]) => UnaryPrefix(op.getIString(), p(right)),
            (is!("var"), [vardefs]) => Var(b(vardefs.getArray().iter().map(|vardef| { (vardef.get(0).getIString(), maybe_parse(vardef.get(1))) }).collect())),
            (is!("while"), [condition, body]) => While(p(condition), p(body)),
            _ => panic!(),
        })
    }

    fn children<'a, 'b: 'a, I>(&'a mut self) -> Box<Iterator<Item=&'a mut AstNode> + 'a> {
        use self::AstValue::*;
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
            If(ref mut cond, ref mut iftrue, ref mut iffalse) => {
                let it = vec![cond, iftrue].into_iter();
                if let Some(ref mut n) = *iffalse { b!(it.chain(iter::once(n))) } else { b!(it.chain(iter::empty())) }
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
        use self::AstValue::*;
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
            If(ref cond, ref iftrue, ref iffalse) => s!("if", cond, iftrue, iffalse),
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
pub fn traversePre<F>(node: &mut AstValue, visit: F) where F: Fn(&mut AstValue) {
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
pub fn traversePrePost<F1,F2>(node: &mut AstValue, visitPre: F1, visitPost: F2) where F1: Fn(&mut AstValue), F2: Fn(&mut AstValue) {
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
fn traversePrePostConditional<F1,F2>(node: &mut AstValue, visitPre: F1, visitPost: F2) where F1: Fn(&mut AstValue) -> bool, F2: Fn(&mut AstValue) {
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

fn traverseFunctions<F>(ast: &mut AstValue, visit: F) where F: Fn(&mut AstValue) {
    match *ast {
        AstValue::Toplevel(ref mut stats) => {
            for curr in stats.iter_mut() {
                if let AstValue::Defun(..) = **curr { visit(curr) }
            }
        },
        AstValue::Defun(..) => visit(ast),
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

// RSTODO
//// JS printer
//struct JSPrinter {
//  bool pretty, finalize;
//
//  char *buffer;
//  int size, used;
//
//  int indent;
//  bool possibleSpace; // add a space to separate identifiers
//
//  Ref ast;
//
//  JSPrinter(bool pretty_, bool finalize_, Ref ast_) : pretty(pretty_), finalize(finalize_), buffer(0), size(0), used(0), indent(0), possibleSpace(false), ast(ast_) {}
//
//  void printAst() {
//    print(ast);
//    buffer[used] = 0;
//  }
//
//  // Utils
//
//  void ensure(int safety=100) {
//    if (size < used + safety) {
//      size = std::max(1024, size*2) + safety;
//      if (!buffer) {
//        buffer = (char*)malloc(size);
//        if (!buffer) {
//          printf("Out of memory allocating %d bytes for output buffer!", size);
//          abort();
//        }
//      } else {
//        char *buf = (char*)realloc(buffer, size);
//        if (!buf) {
//          free(buffer);
//          printf("Out of memory allocating %d bytes for output buffer!", size);
//          abort();
//        }
//        buffer = buf;
//      }
//    }
//  }
//
//  void emit(char c) {
//    maybeSpace(c);
//    if (!pretty && c == '}' && buffer[used-1] == ';') used--; // optimize ;} into }, the ; is not separating anything
//    ensure(1);
//    buffer[used++] = c;
//  }
//
//  void emit(const char *s) {
//    maybeSpace(*s);
//    int len = strlen(s);
//    ensure(len+1);
//    strcpy(buffer + used, s);
//    used += len;
//  }
//
//  void newline() {
//    if (!pretty) return;
//    emit('\n');
//    for (int i = 0; i < indent; i++) emit(' ');
//  }
//
//  void space() {
//    if (pretty) emit(' ');
//  }
//
//  void safeSpace() {
//    if (pretty) emit(' ');
//    else possibleSpace = true;
//  }
//
//  void maybeSpace(char s) {
//    if (possibleSpace) {
//      possibleSpace = false;
//      if (isIdentPart(s)) emit(' ');
//    }
//  }
//
//  void print(Ref node) {
//    ensure();
//    IString type = node[0]->getIString();
//    //fprintf(stderr, "printing %s\n", type.str);
//    switch (type.str[0]) {
//      case 'a': {
//        if (type == ASSIGN) printAssign(node);
//        else if (type == ARRAY) printArray(node);
//        else abort();
//        break;
//      }
//      case 'b': {
//        if (type == BINARY) printBinary(node);
//        else if (type == BLOCK) printBlock(node);
//        else if (type == BREAK) printBreak(node);
//        else abort();
//        break;
//      }
//      case 'c': {
//        if (type == CALL) printCall(node);
//        else if (type == CONDITIONAL) printConditional(node);
//        else if (type == CONTINUE) printContinue(node);
//        else abort();
//        break;
//      }
//      case 'd': {
//        if (type == DEFUN) printDefun(node);
//        else if (type == DO) printDo(node);
//        else if (type == DOT) printDot(node);
//        else abort();
//        break;
//      }
//      case 'i': {
//        if (type == IF) printIf(node);
//        else abort();
//        break;
//      }
//      case 'l': {
//        if (type == LABEL) printLabel(node);
//        else abort();
//        break;
//      }
//      case 'n': {
//        if (type == NAME) printName(node);
//        else if (type == NUM) printNum(node);
//        else if (type == NEW) printNew(node);
//        else abort();
//        break;
//      }
//      case 'o': {
//        if (type == OBJECT) printObject(node);
//        break;
//      }
//      case 'r': {
//        if (type == RETURN) printReturn(node);
//        else abort();
//        break;
//      }
//      case 's': {
//        if (type == STAT) printStat(node);
//        else if (type == SUB) printSub(node);
//        else if (type == SEQ) printSeq(node);
//        else if (type == SWITCH) printSwitch(node);
//        else if (type == STRING) printString(node);
//        else abort();
//        break;
//      }
//      case 't': {
//        if (type == TOPLEVEL) printToplevel(node);
//        else abort();
//        break;
//      }
//      case 'u': {
//        if (type == UNARY_PREFIX) printUnaryPrefix(node);
//        else abort();
//        break;
//      }
//      case 'v': {
//        if (type == VAR) printVar(node);
//        else abort();
//        break;
//      }
//      case 'w': {
//        if (type == WHILE) printWhile(node);
//        else abort();
//        break;
//      }
//      default: {
//        printf("cannot yet print %s\n", type.str);
//        abort();
//      }
//    }
//  }
//
//  // print a node, and if nothing is emitted, emit something instead
//  void print(Ref node, const char *otherwise) {
//    int last = used;
//    print(node);
//    if (used == last) emit(otherwise);
//  }
//
//  void printStats(Ref stats) {
//    bool first = true;
//    for (size_t i = 0; i < stats->size(); i++) {
//      Ref curr = stats[i];
//      if (!isNothing(curr)) {
//        if (first) first = false;
//        else newline();
//        print(stats[i]);
//      }
//    }
//  }
//
//  void printToplevel(Ref node) {
//    if (node[1]->size() > 0) {
//      printStats(node[1]);
//    }
//  }
//
//  void printBlock(Ref node) {
//    if (node->size() == 1 || node[1]->size() == 0) {
//      emit("{}");
//      return;
//    }
//    emit('{');
//    indent++;
//    newline();
//    printStats(node[1]);
//    indent--;
//    newline();
//    emit('}');
//  }
//
//  void printDefun(Ref node) {
//    emit("function ");
//    emit(node[1]->getCString());
//    emit('(');
//    Ref args = node[2];
//    for (size_t i = 0; i < args->size(); i++) {
//      if (i > 0) (pretty ? emit(", ") : emit(','));
//      emit(args[i]->getCString());
//    }
//    emit(')');
//    space();
//    if (node->size() == 3 || node[3]->size() == 0) {
//      emit("{}");
//      return;
//    }
//    emit('{');
//    indent++;
//    newline();
//    printStats(node[3]);
//    indent--;
//    newline();
//    emit('}');
//    newline();
//  }
//
//  bool isNothing(Ref node) {
//    return (node[0] == TOPLEVEL && node[1]->size() == 0) || (node[0] == STAT && isNothing(node[1]));
//  }
//
//  void printStat(Ref node) {
//    if (!isNothing(node[1])) {
//      print(node[1]);
//      if (buffer[used-1] != ';') emit(';');
//    }
//  }
//
//  void printAssign(Ref node) {
//    printChild(node[2], node, -1);
//    space();
//    emit('=');
//    space();
//    printChild(node[3], node, 1);
//  }
//
//  void printName(Ref node) {
//    emit(node[1]->getCString());
//  }
//
//  static char* numToString(double d, bool finalize=true) {
//    bool neg = d < 0;
//    if (neg) d = -d;
//    // try to emit the fewest necessary characters
//    bool integer = fmod(d, 1) == 0;
//    #define BUFFERSIZE 1000
//    static char full_storage_f[BUFFERSIZE], full_storage_e[BUFFERSIZE]; // f is normal, e is scientific for float, x for integer
//    static char *storage_f = full_storage_f + 1, *storage_e = full_storage_e + 1; // full has one more char, for a possible '-'
//    double err_f, err_e;
//    for (int e = 0; e <= 1; e++) {
//      char *buffer = e ? storage_e : storage_f;
//      double temp;
//      if (!integer) {
//        static char format[6];
//        for (int i = 0; i <= 18; i++) {
//          format[0] = '%';
//          format[1] = '.';
//          if (i < 10) {
//            format[2] = '0' + i;
//            format[3] = e ? 'e' : 'f';
//            format[4] = 0;
//          } else {
//            format[2] = '1';
//            format[3] = '0' + (i - 10);
//            format[4] = e ? 'e' : 'f';
//            format[5] = 0;
//          }
//          snprintf(buffer, BUFFERSIZE-1, format, d);
//          sscanf(buffer, "%lf", &temp);
//          //errv("%.18f, %.18e   =>   %s   =>   %.18f, %.18e   (%d), ", d, d, buffer, temp, temp, temp == d);
//          if (temp == d) break;
//        }
//      } else {
//        // integer
//        assert(d >= 0);
//        unsigned long long uu = (unsigned long long)d;
//        if (uu == d) {
//          bool asHex = e && !finalize;
//          snprintf(buffer, BUFFERSIZE-1, asHex ? "0x%llx" : "%llu", uu);
//          if (asHex) {
//            unsigned long long tempULL;
//            sscanf(buffer, "%llx", &tempULL);
//            temp = (double)tempULL;
//          } else {
//            sscanf(buffer, "%lf", &temp);
//          }
//        } else {
//          // too large for a machine integer, just use floats
//          snprintf(buffer, BUFFERSIZE-1, e ? "%e" : "%.0f", d); // even on integers, e with a dot is useful, e.g. 1.2e+200
//          sscanf(buffer, "%lf", &temp);
//        }
//        //errv("%.18f, %.18e   =>   %s   =>   %.18f, %.18e, %llu   (%d)\n", d, d, buffer, temp, temp, uu, temp == d);
//      }
//      (e ? err_e : err_f) = fabs(temp - d);
//      //errv("current attempt: %.18f  =>  %s", d, buffer);
//      //assert(temp == d);
//      char *dot = strchr(buffer, '.');
//      if (dot) {
//        // remove trailing zeros
//        char *end = dot+1;
//        while (*end >= '0' && *end <= '9') end++;
//        end--;
//        while (*end == '0') {
//          char *copy = end;
//          do {
//            copy[0] = copy[1];
//          } while (*copy++ != 0);
//          end--;
//        }
//        //errv("%.18f  =>   %s", d, buffer);
//        // remove preceding zeros
//        while (*buffer == '0') {
//          char *copy = buffer;
//          do {
//            copy[0] = copy[1];
//          } while (*copy++ != 0);
//        }
//        //errv("%.18f ===>  %s", d, buffer);
//      } else if (!integer || !e) {
//        // no dot. try to change 12345000 => 12345e3
//        char *end = strchr(buffer, 0);
//        end--;
//        char *test = end;
//        // remove zeros, and also doubles can use at most 24 digits, we can truncate any extras even if not zero
//        while ((*test == '0' || test - buffer > 24) && test > buffer) test--;
//        int num = end - test;
//        if (num >= 3) {
//          test++;
//          test[0] = 'e';
//          if (num < 10) {
//            test[1] = '0' + num;
//            test[2] = 0;
//          } else if (num < 100) {
//            test[1] = '0' + (num / 10);
//            test[2] = '0' + (num % 10);
//            test[3] = 0;
//          } else {
//            assert(num < 1000);
//            test[1] = '0' + (num / 100);
//            test[2] = '0' + (num % 100) / 10;
//            test[3] = '0' + (num % 10);
//            test[4] = 0;
//          }
//        }
//      }
//      //errv("..current attempt: %.18f  =>  %s", d, buffer);
//    }
//    //fprintf(stderr, "options:\n%s\n%s\n (first? %d)\n", storage_e, storage_f, strlen(storage_e) < strlen(storage_f));
//    char *ret;
//    if (err_e == err_f) {
//      ret = strlen(storage_e) < strlen(storage_f) ? storage_e : storage_f;
//    } else {
//      ret = err_e < err_f ? storage_e : storage_f;
//    }
//    if (neg) {
//      ret--; // safe to go back one, there is one more char in full_*
//      *ret = '-';
//    }
//    return ret;
//  }
//
//  void printNum(Ref node) {
//    emit(numToString(node[1]->getNumber(), finalize));
//  }
//
//  void printString(Ref node) {
//    emit('"');
//    emit(node[1]->getCString());
//    emit('"');
//  }
//
//  // Parens optimizing
//
//  bool capturesOperators(Ref node) {
//    Ref type = node[0];
//    return type == CALL || type == ARRAY || type == OBJECT || type == SEQ;
//  }
//
//  int getPrecedence(Ref node, bool parent) {
//    Ref type = node[0];
//    if (type == BINARY || type == UNARY_PREFIX) {
//      return OperatorClass::getPrecedence(type == BINARY ? OperatorClass::Binary : OperatorClass::Prefix, node[1]->getIString());
//    } else if (type == SEQ) {
//      return OperatorClass::getPrecedence(OperatorClass::Binary, COMMA);
//    } else if (type == CALL) {
//      return parent ? OperatorClass::getPrecedence(OperatorClass::Binary, COMMA) : -1; // call arguments are split by commas, but call itself is safe
//    } else if (type == ASSIGN) {
//      return OperatorClass::getPrecedence(OperatorClass::Binary, SET);
//    } else if (type == CONDITIONAL) {
//      return OperatorClass::getPrecedence(OperatorClass::Tertiary, QUESTION);
//    }
//    // otherwise, this is something that fixes precedence explicitly, and we can ignore
//    return -1; // XXX
//  }
//
//  // check whether we need parens for the child, when rendered in the parent
//  // @param childPosition -1 means it is printed to the left of parent, 0 means "anywhere", 1 means right
//  bool needParens(Ref parent, Ref child, int childPosition) {
//    int parentPrecedence = getPrecedence(parent, true);
//    int childPrecedence = getPrecedence(child, false);
//
//    if (childPrecedence > parentPrecedence) return true;  // child is definitely a danger
//    if (childPrecedence < parentPrecedence) return false; //          definitely cool
//    // equal precedence, so associativity (rtl/ltr) is what matters
//    // (except for some exceptions, where multiple operators can combine into confusion)
//    if (parent[0] == UNARY_PREFIX) {
//      assert(child[0] == UNARY_PREFIX);
//      if ((parent[1] == PLUS || parent[1] == MINUS) && child[1] == parent[1]) {
//        // cannot emit ++x when we mean +(+x)
//        return true;
//      }
//    }
//    if (childPosition == 0) return true; // child could be anywhere, so always paren
//    if (childPrecedence < 0) return false; // both precedences are safe
//    // check if child is on the dangerous side
//    if (OperatorClass::getRtl(parentPrecedence)) return childPosition < 0;
//    else return childPosition > 0;
//  }
//
//  void printChild(Ref child, Ref parent, int childPosition=0) {
//    bool parens = needParens(parent, child, childPosition);
//    if (parens) emit('(');
//    print(child);
//    if (parens) emit(')');
//  }
//
//  void printBinary(Ref node) {
//    printChild(node[2], node, -1);
//    space();
//    emit(node[1]->getCString());
//    space();
//    printChild(node[3], node, 1);
//  }
//
//  void printUnaryPrefix(Ref node) {
//    if (finalize && node[1] == PLUS && (node[2][0] == NUM ||
//                                       (node[2][0] == UNARY_PREFIX && node[2][1] == MINUS && node[2][2][0] == NUM))) {
//      // emit a finalized number
//      int last = used;
//      print(node[2]);
//      ensure(1); // we temporarily append a 0
//      char *curr = buffer + last; // ensure might invalidate
//      buffer[used] = 0;
//      if (strchr(curr, '.')) return; // already a decimal point, all good
//      char *e = strchr(curr, 'e');
//      if (!e) {
//        emit(".0");
//        return;
//      }
//      ensure(3);
//      curr = buffer + last; // ensure might invalidate
//      char *end = strchr(curr, 0);
//      while (end >= e) {
//        end[2] = end[0];
//        end--;
//      }
//      e[0] = '.';
//      e[1] = '0';
//      used += 2;
//      return;
//    }
//    if ((buffer[used-1] == '-' && node[1] == MINUS) ||
//        (buffer[used-1] == '+' && node[1] == PLUS)) {
//      emit(' '); // cannot join - and - to --, looks like the -- operator
//    }
//    emit(node[1]->getCString());
//    printChild(node[2], node, 1);
//  }
//
//  void printConditional(Ref node) {
//    printChild(node[1], node, -1);
//    space();
//    emit('?');
//    space();
//    printChild(node[2], node, 0);
//    space();
//    emit(':');
//    space();
//    printChild(node[3], node, 1);
//  }
//
//  void printCall(Ref node) {
//    printChild(node[1], node, 0);
//    emit('(');
//    Ref args = node[2];
//    for (size_t i = 0; i < args->size(); i++) {
//      if (i > 0) (pretty ? emit(", ") : emit(','));
//      printChild(args[i], node, 0);
//    }
//    emit(')');
//  }
//
//  void printSeq(Ref node) {
//    printChild(node[1], node, -1);
//    emit(',');
//    space();
//    printChild(node[2], node, 1);
//  }
//
//  void printDot(Ref node) {
//    print(node[1]);
//    emit('.');
//    emit(node[2]->getCString());
//  }
//
//  void printSwitch(Ref node) {
//    emit("switch");
//    space();
//    emit('(');
//    print(node[1]);
//    emit(')');
//    space();
//    emit('{');
//    newline();
//    Ref cases = node[2];
//    for (size_t i = 0; i < cases->size(); i++) {
//      Ref c = cases[i];
//      if (!c[0]) {
//        emit("default:");
//      } else {
//        emit("case ");
//        print(c[0]);
//        emit(':');
//      }
//      if (c[1]->size() > 0) {
//        indent++;
//        newline();
//        int curr = used;
//        printStats(c[1]);
//        indent--;
//        if (curr != used) newline();
//        else used--; // avoid the extra indentation we added tentatively
//      } else {
//        newline();
//      }
//    }
//    emit('}');
//  }
//
//  void printSub(Ref node) {
//    printChild(node[1], node, -1);
//    emit('[');
//    print(node[2]);
//    emit(']');
//  }
//
//  void printVar(Ref node) {
//    emit("var ");
//    Ref args = node[1];
//    for (size_t i = 0; i < args->size(); i++) {
//      if (i > 0) (pretty ? emit(", ") : emit(','));
//      emit(args[i][0]->getCString());
//      if (args[i]->size() > 1) {
//        space();
//        emit('=');
//        space();
//        print(args[i][1]);
//      }
//    }
//    emit(';');
//  }
//
//  static bool ifHasElse(Ref node) {
//    assert(node[0] == IF);
//    return node->size() >= 4 && !!node[3];
//  }
//
//  void printIf(Ref node) {
//    emit("if");
//    safeSpace();
//    emit('(');
//    print(node[1]);
//    emit(')');
//    space();
//    // special case: we need braces to save us from ambiguity, if () { if () } else. otherwise else binds to inner if
//    // also need to recurse for                                if () { if () { } else { if () } else
//    // (note that this is only a problem if the if body has a single element in it, not a block or such, as then
//    // the block would be braced)
//    // this analysis is a little conservative - it assumes any child if could be confused with us, which implies
//    // all other braces vanished (the worst case for us, we are not saved by other braces).
//    bool needBraces = false;
//    bool hasElse = ifHasElse(node);
//    if (hasElse) {
//      Ref child = node[2];
//      while (child[0] == IF) {
//        if (!ifHasElse(child)) {
//          needBraces = true;
//          break;
//        }
//        child = child[3]; // continue into the else
//      }
//    }
//    if (needBraces) {
//      emit('{');
//      indent++;
//      newline();
//      print(node[2]);
//      indent--;
//      newline();
//      emit('}');
//    } else {
//      print(node[2], "{}");
//    }
//    if (hasElse) {
//      space();
//      emit("else");
//      safeSpace();
//      print(node[3], "{}");
//    }
//  }
//
//  void printDo(Ref node) {
//    emit("do");
//    safeSpace();
//    print(node[2], "{}");
//    space();
//    emit("while");
//    space();
//    emit('(');
//    print(node[1]);
//    emit(')');
//    emit(';');
//  }
//
//  void printWhile(Ref node) {
//    emit("while");
//    space();
//    emit('(');
//    print(node[1]);
//    emit(')');
//    space();
//    print(node[2], "{}");
//  }
//
//  void printLabel(Ref node) {
//    emit(node[1]->getCString());
//    space();
//    emit(':');
//    space();
//    print(node[2]);
//  }
//
//  void printReturn(Ref node) {
//    emit("return");
//    if (!!node[1]) {
//      emit(' ');
//      print(node[1]);
//    }
//    emit(';');
//  }
//
//  void printBreak(Ref node) {
//    emit("break");
//    if (!!node[1]) {
//      emit(' ');
//      emit(node[1]->getCString());
//    }
//    emit(';');
//  }
//
//  void printContinue(Ref node) {
//    emit("continue");
//    if (!!node[1]) {
//      emit(' ');
//      emit(node[1]->getCString());
//    }
//    emit(';');
//  }
//
//  void printNew(Ref node) {
//    emit("new ");
//    print(node[1]);
//  }
//
//  void printArray(Ref node) {
//    emit('[');
//    Ref args = node[1];
//    for (size_t i = 0; i < args->size(); i++) {
//      if (i > 0) (pretty ? emit(", ") : emit(','));
//      print(args[i]);
//    }
//    emit(']');
//  }
//
//  void printObject(Ref node) {
//    emit('{');
//    indent++;
//    newline();
//    Ref args = node[1];
//    for (size_t i = 0; i < args->size(); i++) {
//      if (i > 0) {
//        pretty ? emit(", ") : emit(',');
//        newline();
//      }
//      emit('"');
//      emit(args[i][0]->getCString());
//      emit("\":");
//      space();
//      print(args[i][1]);
//    }
//    indent--;
//    newline();
//    emit('}');
//  }
//};

// cashew builder
pub mod builder {

    use super::super::IString;
    use super::{AstNode, AstValue, AstVec};

    fn is_statable(av: &AstValue) -> bool {
        use super::AstValue::*;
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
            AstValue::Toplevel(ref mut s) => *s = stats,
            AstValue::Defun(_, _, ref mut s) => *s = stats,
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
