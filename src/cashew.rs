use std::collections::HashMap;
use std::io::Write;
use std::iter;
use std::mem;
use std::ptr;
use std::ops::{Deref, DerefMut};

use odds::vec::VecExt;

use string_cache::Atom;

use serde_json;

#[derive(Clone, Eq, PartialEq)]
struct Ref {
    inst: *mut Value,
}

impl Ref {
    fn new(v: *mut Value) -> Ref { // can be null
        Ref { inst: v }
    }
    fn get(&self) -> &Value {
        unsafe { &(*self.inst) }
    }
    fn get_mut(&self) -> &mut Value {
        unsafe { &mut (*self.inst) }
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
        self.get()
    }
}
impl DerefMut for Ref {
    fn deref_mut(&mut self) -> &mut Value {
        self.get_mut()
    }
}

const EMPTYREF: Ref = Ref { inst: ptr::null_mut() };

// Arena allocation, free it all on process exit

type ArrayStorage = Vec<Ref>;

const ARENA_CHUNK_SIZE: usize = 1000;
struct Arena {
    chunks: Vec<*const Value>,
    index: usize, // in last chunk

    arr_chunks: Vec<Box<ArrayStorage>>,
    arr_index: usize,
}

impl Arena {
    fn new() -> Arena {
        Arena { chunks: vec![], index: 0, arr_chunks: vec![], arr_index: 0 }
    }
    // RSTODO: placeholder
    fn allocArray(&self) -> ArrayStorage {
        vec![]
    }
    // RSTODO: placeholder
    fn alloc(&self) -> Ref {
        let mut v = Value::new();
        let r = Ref { inst: &mut v as *mut Value };
        mem::forget(v);
        r
    }
}

// RSTODO: remove
// this allows the lazy_static
unsafe impl Sync for Arena {}

lazy_static! {
    static ref ARENA: Arena = Arena::new();
}

type ObjectStorage = HashMap<Atom, Ref>;

enum Value {
    null,
    str(Atom),
    num(f64),
    arr(ArrayStorage),
    boo(bool),
    obj(ObjectStorage),
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match self {
            &Value::str(_) |
            &Value::num(_) |
            &Value::null |
            &Value::boo(_) => self == other,
            // if you want a deep compare, use deepCompare
            // RSTODO: this is unfortunate
            &Value::arr(_) |
            &Value::obj(_) => self as *const Value == other as *const Value,
        }
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        self.free();
    }
}

// RSTODO: are the return values needed in set* and assignFrom?
impl Value {
    fn new() -> Value {
        Value::null
    }
    fn free(&mut self) {
        if let &mut Value::arr(ref mut a) = self {
            a.truncate(0);
            a.shrink_to_fit();
        }
        *self = Value::null;
    }

    fn from_str(s: &str) -> Value {
        let mut v = Value::new();
        v.setString(s);
        v
    }
    fn from_double(n: f64) -> Value {
        let mut v = Value::new();
        v.setNumber(n);
        v
    }
    fn from_arraystorage(a: &ArrayStorage) -> Value {
        let mut v = Value::new();
        v.setArray(a);
        v
    }

    fn setString(&mut self, s: &str) -> &mut Value {
        self.free();
        *self = Value::str(Atom::from(s));
        self
    }
    fn setAtom(&mut self, a: Atom) -> &mut Value {
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
    fn setArrayHint(&mut self, size_hint: usize) -> &mut Value {
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
    fn setBool(&mut self, b: bool) -> &mut Value {
        self.free();
        *self = Value::boo(b);
        self
    }
    fn setObject(&mut self) -> &mut Value {
        self.free();
        *self = Value::obj(ObjectStorage::new());
        self
    }

    fn isString(&self) -> bool {
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

    fn getStr(&self) -> &str {
        if let &Value::str(ref a) = self { &*a } else { panic!() }
    }
    fn getAtom(&self) -> Atom {
        if let &Value::str(ref a) = self { a.clone() } else { panic!() }
    }
    fn getNumber(&self) -> f64 {
        if let &Value::num(d) = self { d } else { panic!() }
    }
    fn getBool(&self) -> bool {
        if let &Value::boo(b) = self { b } else { panic!() }
    }
    fn getArray(&self) -> &ArrayStorage {
        if let &Value::arr(ref a) = self { a } else { panic!() }
    }
    fn getMutArray(&mut self) -> &mut ArrayStorage {
        if let &mut Value::arr(ref mut a) = self { a } else { panic!() }
    }
    fn getObject(&self) -> &ObjectStorage {
        if let &Value::obj(ref o) = self { o } else { panic!() }
    }
    fn getMutObject(&mut self) -> &mut ObjectStorage {
        if let &mut Value::obj(ref mut o) = self { o } else { panic!() }
    }

    // convenience function to get a known integer
    fn getInteger(&self) -> i64 {
        let d = self.getNumber();
        assert!(d % 1.0 == 0.0);
        let ret = d as i64;
        assert!(ret as f64 == d); // no loss in conversion
        ret
    }

    fn assignFrom(&mut self, other: &Value) -> &Value {
        self.free();
        match other {
            &Value::null => self.setNull(),
            &Value::str(ref a) => self.setAtom(a.clone()),
            &Value::num(d) => self.setNumber(d),
            &Value::arr(ref a) => self.setArray(a),
            &Value::boo(b) => self.setBool(b),
            &Value::obj(_) => panic!(), // TODO
        };
        self
    }

    // RSTODO
    fn deepCompare(&self, otherref: Ref) -> bool {
        false
    }
//  bool deepCompare(Ref ref) {
//    Value& other = *ref;
//    if (*this == other) return true; // either same pointer, or identical value type (string, number, null or bool)
//    if (type != other.type) return false;
//    if (type == Array) {
//      if (arr->size() != other.arr->size()) return false;
//      for (unsigned i = 0; i < arr->size(); i++) {
//        if (!(*arr)[i]->deepCompare((*other.arr)[i])) return false;
//      }
//      return true;
//    } else if (type == Object) {
//      if (obj->size() != other.obj->size()) return false;
//      for (auto i : *obj) {
//        if (other.obj->count(i.first) == 0) return false;
//        if (i.second->deepCompare((*other.obj)[i.first])) return false;
//      }
//      return true;
//    }
//    return false;
//  }


    fn parse(&mut self, curr: &str) {
        let json: serde_json::Value = serde_json::from_str(curr).unwrap();
        self.parse_json(&json);
    }
    fn parse_json(&mut self, json: &serde_json::Value) {
        match json {
            &serde_json::Value::Null => self.setNull(),
            &serde_json::Value::Bool(b) => self.setBool(b),
            &serde_json::Value::I64(n) => self.setNumber(n as f64),
            &serde_json::Value::U64(n) => self.setNumber(n as f64),
            &serde_json::Value::F64(n) => self.setNumber(n),
            &serde_json::Value::String(ref s) => self.setString(s),
            &serde_json::Value::Array(ref a) => {
                self.setArrayHint(a.len());
                {
                    let mut sa = match self {
                        &mut Value::arr(ref mut sa) => sa,
                        _ => unreachable!(),
                    };
                    for v in a {
                        let mut tmp: Ref = ARENA.alloc();
                        tmp.parse_json(v);
                        sa.push(tmp);
                    };
                }
                self
            },
            &serde_json::Value::Object(ref o) => {
                self.setNull()
            },
        };
    }

    fn stringify<T>(&self, mut out: T, pretty: bool) where T: Write {
        let jsonobj = self.stringify_json();
        let outstr = if pretty {
            serde_json::ser::to_string(&jsonobj)
        } else {
            serde_json::ser::to_string_pretty(&jsonobj)
        }.unwrap();
        out.write(outstr.as_bytes()); // .unwrap
    }
    fn stringify_json(&self) -> serde_json::Value {
        match self {
            &Value::null =>   serde_json::Value::Null,
            &Value::str(ref a) => serde_json::Value::String((&**a).to_string()),
            &Value::num(n) => serde_json::Value::F64(n),
            &Value::boo(b) => serde_json::Value::Bool(b),
            &Value::arr(ref a) => {
                let outvec = a.iter().map(|v| v.stringify_json()).collect();
                serde_json::Value::Array(outvec)
            },
            &Value::obj(ref o) => {
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

    fn size(&self) -> usize {
        self.getArray().len()
    }

    fn setSize(&mut self, size: usize) {
        let a = self.getMutArray();
        let old = a.len();
        if old < size {
            a.reserve_exact(size - old);
        }
        for i in old..size {
            a.push(ARENA.alloc());
        }
    }

    fn get(&self, x: usize) -> Ref {
        self.getArray().get(x).unwrap().clone()
    }

    fn push_back(&mut self, r: Ref) -> &Value {
        self.getMutArray().push(r);
        self
    }

    fn pop_back(&mut self) -> Ref {
        self.getMutArray().pop().unwrap()
    }

    fn back(&self) -> Option<Ref> {
        match self.getArray().last() {
            Some(r) => Some(r.clone()),
            None => None,
        }
    }

    fn splice(&mut self, x: usize, num: usize) {
        self.getMutArray().splice(x..x+num, iter::empty());
    }

    fn insertEmpties(&mut self, x: usize, num: usize) {
        let empties: Vec<_> = iter::repeat(EMPTYREF).take(num).collect();
        self.getMutArray().splice(x..x, empties.into_iter());
    }

    fn insert(&mut self, x: usize, node: Ref) {
        self.getMutArray().insert(x, node);
    }

    fn indexOf(&self, other: Ref) -> isize {
        match self.getArray().iter().position(|r| r.clone() == other) {
            Some(i) => i as isize,
            None => -1,
        }
    }

    fn map<F>(&self, func: F) -> Ref where F: Fn(Ref) -> Ref {
        let a = self.getArray();
        let mut ret = ARENA.alloc();
        ret.setArrayHint(a.len());
        {
            let mut retarr = ret.getMutArray();
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
            let mut retarr = ret.getMutArray();
            for r in a {
                if func(r.clone()) { retarr.push(r.clone()) }
            }
        }
        ret
    }

    // Null operations

    // Bool operations

    // Object operations

    fn lookup(&mut self, x: Atom) -> Ref {
        self.getMutObject().entry(x).or_insert(EMPTYREF).clone()
    }

    fn has(&self, x: Atom) -> bool {
        self.getObject().contains_key(&x)
    }
}

//// AST traversals
//
//// Traverse, calling visit before the children
//void traversePre(Ref node, std::function<void (Ref)> visit);
//
//// Traverse, calling visitPre before the children and visitPost after
//void traversePrePost(Ref node, std::function<void (Ref)> visitPre, std::function<void (Ref)> visitPost);
//
//// Traverse, calling visitPre before the children and visitPost after. If pre returns false, do not traverse children
//void traversePrePostConditional(Ref node, std::function<bool (Ref)> visitPre, std::function<void (Ref)> visitPost);
//
//// Traverses all the top-level functions in the document
//void traverseFunctions(Ref ast, std::function<void (Ref)> visit);
//
//// JS printer
//
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
//
//// cashew builder
//
//class ValueBuilder {
//  static IStringSet statable;
//
//  static Ref makeRawString(const IString& s) {
//    return &arena.alloc()->setString(s);
//  }
//
//  static Ref makeRawArray(int size_hint=0) {
//    return &arena.alloc()->setArray(size_hint);
//  }
//
//  static Ref makeNull() {
//    return &arena.alloc()->setNull();
//  }
//
//public:
//  static Ref makeToplevel() {
//    return &makeRawArray(2)->push_back(makeRawString(TOPLEVEL))
//                            .push_back(makeRawArray());
//  }
//
//  static Ref makeString(IString str) {
//    return &makeRawArray(2)->push_back(makeRawString(STRING))
//                            .push_back(makeRawString(str));
//  }
//
//  static Ref makeBlock() {
//    return &makeRawArray(2)->push_back(makeRawString(BLOCK))
//                            .push_back(makeRawArray());
//  }
//
//  static Ref makeName(IString name) {
//    return &makeRawArray(2)->push_back(makeRawString(NAME))
//                            .push_back(makeRawString(name));
//  }
//
//  static void setBlockContent(Ref target, Ref block) {
//    if (target[0] == TOPLEVEL) {
//      target[1]->setArray(block[1]->getArray());
//    } else if (target[0] == DEFUN) {
//      target[3]->setArray(block[1]->getArray());
//    } else abort();
//  }
//
//  static void appendToBlock(Ref block, Ref element) {
//    assert(block[0] == BLOCK);
//    block[1]->push_back(element);
//  }
//
//  static Ref makeCall(Ref target) {
//    return &makeRawArray(3)->push_back(makeRawString(CALL))
//                            .push_back(target)
//                            .push_back(makeRawArray());
//  }
//
//  static void appendToCall(Ref call, Ref element) {
//    assert(call[0] == CALL);
//    call[2]->push_back(element);
//  }
//
//  static Ref makeStatement(Ref contents) {
//    if (statable.has(contents[0]->getIString())) {
//      return &makeRawArray(2)->push_back(makeRawString(STAT))
//                              .push_back(contents);
//    } else {
//      return contents; // only very specific things actually need to be stat'ed
//    }
//  }
//
//  static Ref makeDouble(double num) {
//    return &makeRawArray(2)->push_back(makeRawString(NUM))
//                            .push_back(&arena.alloc()->setNumber(num));
//  }
//  static Ref makeInt(uint32_t num) {
//    return makeDouble(double(num));
//  }
//
//  static Ref makeBinary(Ref left, IString op, Ref right) {
//    if (op == SET) {
//      return &makeRawArray(4)->push_back(makeRawString(ASSIGN))
//                              .push_back(&arena.alloc()->setBool(true))
//                              .push_back(left)
//                              .push_back(right);
//    } else if (op == COMMA) {
//      return &makeRawArray(3)->push_back(makeRawString(SEQ))
//                              .push_back(left)
//                              .push_back(right);
//    } else {
//      return &makeRawArray(4)->push_back(makeRawString(BINARY))
//                              .push_back(makeRawString(op))
//                              .push_back(left)
//                              .push_back(right);
//    }
//  }
//
//  static Ref makePrefix(IString op, Ref right) {
//    return &makeRawArray(3)->push_back(makeRawString(UNARY_PREFIX))
//                            .push_back(makeRawString(op))
//                            .push_back(right);
//  }
//
//  static Ref makeFunction(IString name) {
//    return &makeRawArray(4)->push_back(makeRawString(DEFUN))
//                            .push_back(makeRawString(name))
//                            .push_back(makeRawArray())
//                            .push_back(makeRawArray());
//  }
//
//  static void appendArgumentToFunction(Ref func, IString arg) {
//    assert(func[0] == DEFUN);
//    func[2]->push_back(makeRawString(arg));
//  }
//
//  static Ref makeVar(bool is_const) {
//    return &makeRawArray(2)->push_back(makeRawString(VAR))
//                            .push_back(makeRawArray());
//  }
//
//  static void appendToVar(Ref var, IString name, Ref value) {
//    assert(var[0] == VAR);
//    Ref array = &makeRawArray(1)->push_back(makeRawString(name));
//    if (!!value) array->push_back(value);
//    var[1]->push_back(array);
//  }
//
//  static Ref makeReturn(Ref value) {
//    return &makeRawArray(2)->push_back(makeRawString(RETURN))
//                            .push_back(!!value ? value : makeNull());
//  }
//
//  static Ref makeIndexing(Ref target, Ref index) {
//    return &makeRawArray(3)->push_back(makeRawString(SUB))
//                            .push_back(target)
//                            .push_back(index);
//  }
//
//  static Ref makeIf(Ref condition, Ref ifTrue, Ref ifFalse) {
//    return &makeRawArray(4)->push_back(makeRawString(IF))
//                            .push_back(condition)
//                            .push_back(ifTrue)
//                            .push_back(!!ifFalse ? ifFalse : makeNull());
//  }
//
//  static Ref makeConditional(Ref condition, Ref ifTrue, Ref ifFalse) {
//    return &makeRawArray(4)->push_back(makeRawString(CONDITIONAL))
//                            .push_back(condition)
//                            .push_back(ifTrue)
//                            .push_back(ifFalse);
//  }
//
//  static Ref makeDo(Ref body, Ref condition) {
//    return &makeRawArray(3)->push_back(makeRawString(DO))
//                            .push_back(condition)
//                            .push_back(body);
//  }
//
//  static Ref makeWhile(Ref condition, Ref body) {
//    return &makeRawArray(3)->push_back(makeRawString(WHILE))
//                            .push_back(condition)
//                            .push_back(body);
//  }
//
//  static Ref makeBreak(IString label) {
//    return &makeRawArray(2)->push_back(makeRawString(BREAK))
//                            .push_back(!!label ? makeRawString(label) : makeNull());
//  }
//
//  static Ref makeContinue(IString label) {
//    return &makeRawArray(2)->push_back(makeRawString(CONTINUE))
//                            .push_back(!!label ? makeRawString(label) : makeNull());
//  }
//
//  static Ref makeLabel(IString name, Ref body) {
//    return &makeRawArray(3)->push_back(makeRawString(LABEL))
//                            .push_back(makeRawString(name))
//                            .push_back(body);
//  }
//
//  static Ref makeSwitch(Ref input) {
//    return &makeRawArray(3)->push_back(makeRawString(SWITCH))
//                            .push_back(input)
//                            .push_back(makeRawArray());
//  }
//
//  static void appendCaseToSwitch(Ref switch_, Ref arg) {
//    assert(switch_[0] == SWITCH);
//    switch_[2]->push_back(&makeRawArray(2)->push_back(arg)
//                                           .push_back(makeRawArray()));
//  }
//
//  static void appendDefaultToSwitch(Ref switch_) {
//    assert(switch_[0] == SWITCH);
//    switch_[2]->push_back(&makeRawArray(2)->push_back(makeNull())
//                                           .push_back(makeRawArray()));
//  }
//
//  static void appendCodeToSwitch(Ref switch_, Ref code, bool explicitBlock) {
//    assert(switch_[0] == SWITCH);
//    assert(code[0] == BLOCK);
//    if (!explicitBlock) {
//      for (size_t i = 0; i < code[1]->size(); i++) {
//        switch_[2]->back()->back()->push_back(code[1][i]);
//      }
//    } else {
//      switch_[2]->back()->back()->push_back(code);
//    }
//  }
//
//  static Ref makeDot(Ref obj, IString key) {
//    return &makeRawArray(3)->push_back(makeRawString(DOT))
//                            .push_back(obj)
//                            .push_back(makeRawString(key));
//  }
//
//  static Ref makeDot(Ref obj, Ref key) {
//    assert(key[0] == NAME);
//    return makeDot(obj, key[1]->getIString());
//  }
//
//  static Ref makeNew(Ref call) {
//    return &makeRawArray(2)->push_back(makeRawString(NEW))
//                            .push_back(call);
//  }
//
//  static Ref makeArray() {
//    return &makeRawArray(2)->push_back(makeRawString(ARRAY))
//                            .push_back(makeRawArray());
//  }
//
//  static void appendToArray(Ref array, Ref element) {
//    assert(array[0] == ARRAY);
//    array[1]->push_back(element);
//  }
//
//  static Ref makeObject() {
//    return &makeRawArray(2)->push_back(makeRawString(OBJECT))
//                            .push_back(makeRawArray());
//  }
//
//  static void appendToObject(Ref array, IString key, Ref value) {
//    assert(array[0] == OBJECT);
//    array[1]->push_back(&makeRawArray(2)->push_back(makeRawString(key))
//                                         .push_back(value));
//  }
//};
//
//// Tolerates 0.0 in the input; does not trust a +() to be there.
//class DotZeroValueBuilder : public ValueBuilder {
//public:
//  static Ref makeDouble(double num) {
//    return makePrefix(PLUS, ValueBuilder::makeDouble(num));
//  }
//};
//
//} // namespace cashew
//
//
