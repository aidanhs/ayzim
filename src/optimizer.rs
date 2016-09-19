use std::cell::{Cell, UnsafeCell};
use std::cmp;
use std::collections::{HashMap, HashSet, hash_map};
use std::{f64, i32};
#[cfg(feature = "profiling")]
use std::io::Write;
use std::iter;
use std::mem;
use std::ptr;
#[cfg(feature = "profiling")]
use std::time::{Duration, SystemTime};

use odds::vec::VecExt;

use phf;

use serde_json;

use super::IString;
#[cfg(feature = "profiling")]
use super::MoreTime;
use super::cashew::{AstValue, AstNode, AstVec};
use super::cashew::AstValue::*;
use super::cashew::{traversePre, traversePreMut, traversePrePostMut, traversePrePostConditionalMut, traverseFunctionsMut};
use super::cashew::builder;
use super::num::{jsD2I, f64toi32, f64tou32, isInteger, isInteger32};

const NUM_ASMTYPES: usize = 12;
#[derive(Copy, Clone, PartialEq, Eq)]
enum AsmType {
    Int,
    Double,
    Float,
    Float32x4,
    Float64x2,
    Int8x16,
    Int16x8,
    Int32x4,
    Bool8x16,
    Bool16x8,
    Bool32x4,
    Bool64x2,
}
// RSTODO
//AsmType intToAsmType(int type) {
//  if (type >= 0 && type <= ASM_NONE) return (AsmType)type;
//  else {
//    assert(0);
//    return ASM_NONE;
//  }
//}

struct Local {
    ty: AsmType,
    param: bool, // false if a var
}

impl Local {
    fn new(ty: AsmType, param: bool) -> Self {
        Local { ty: ty, param: param }
    }
}

struct AsmData<'a> {
    locals: HashMap<IString, Local>,
    params: Vec<IString>, // in order
    vars: Vec<IString>, // in order
    ret: Option<AsmType>,

    func: &'a mut AstValue,
    floatZero: Option<IString>,
}

impl<'a> AsmData<'a> {
    // if you want to read data from f, and modify it as you go (parallel to denormalize)
    fn new(f: &mut AstValue) -> AsmData {
        let mut locals = HashMap::new();
        let mut params = vec![];
        let mut vars = vec![];
        let ret;
        let func = f;
        let mut floatZero = None;

        {
        let (_, fnparams, stats) = func.getMutDefun();
        let fnparams: &AstVec<_> = fnparams;
        let mut stati = 0;

        // process initial params
        for stat in stats[stati..].iter_mut() {
            {
            let (name, val) = if let mast!(Stat(Assign(_, Name(ref name), ref val))) = *stat { (name, val) } else { break };
            let index = fnparams.iter().position(|p| p == name);
            // not an assign into a parameter, but a global?
            if index.is_none() { break }
            // already done that param, must be starting function body?
            if locals.contains_key(name) { break }
            params.push(name.clone());
            let localty = detectType(val, None, &mut floatZero, false);
            // RSTODO: valid to not have type?
            let prev = locals.insert(name.clone(), Local::new(localty.unwrap(), true));
            assert!(prev.is_none());
            }
            *stat = makeEmpty();
            stati += 1
        }

        // process initial variable definitions and remove '= 0' etc parts -
        // these are not actually assignments in asm.js
        'outside: for stat in stats[stati..].iter_mut() {
            let statvars = if let Var(ref mut vars) = **stat { vars } else { break };
            let mut first = true;
            for &mut (ref name, ref mut val) in statvars.iter_mut() {
                if !locals.contains_key(name) {
                    vars.push(name.clone());
                    let val = val.take().unwrap(); // make an un-assigning var
                    let localty = detectType(&val, None, &mut floatZero, false);
                    // RSTODO: valid to not have type?
                    let prev = locals.insert(name.clone(), Local::new(localty.unwrap(), false));
                    assert!(prev.is_none());
                } else {
                    assert!(first); // cannot break in the middle
                    break 'outside
                }
                first = false
            }
            stati += 1
        }

        // look for other var definitions and collect them
        for stat in stats[stati..].iter_mut() {
            traversePre(stat, |node| {
                if let Var(..) = *node {
                    println!("{:?}", node);
                    panic!()
                    // dump("bad, seeing a var in need of fixing", func);
                    //, 'should be no vars to fix! ' + func[1] + ' : ' + JSON.stringify(node));
                }
            });
            stati += 1
        }

        // look for final RETURN statement to get return type.
        ret = stats.last().map_or(None, |retStmt| {
            if let Return(Some(ref retval)) = **retStmt {
                detectType(retval, None, &mut floatZero, false)
            } else {
                None
            }
        })
        }

        AsmData {
            locals: locals,
            params: params,
            vars: vars,
            ret: ret,

            func: func,
            floatZero: floatZero,
        }
    }

    fn denormalize(&mut self) {
        let (_, params, stats) = self.func.getMutDefun();

        // Remove var definitions, if any
        for stat in stats.iter_mut() {
            if let Var(..) = **stat {
                *stat = makeEmpty()
            } else if !isEmpty(stat) {
                break
            }
        }

        // calculate variable definitions
        let mut varDefs = makeArray(self.vars.len());
        for v in &self.vars {
            let localty = self.locals.get(v).unwrap().ty;
            let zero = makeAsmCoercedZero(localty, self.floatZero.clone());
            varDefs.push((v.clone(), Some(zero)));
        }

        // each param needs a line; reuse emptyNodes as much as we can
        let numParams = self.params.len();
        let mut emptyNodes = 0;
        while emptyNodes < stats.len() {
            if !isEmpty(&stats[emptyNodes]) { break }
            emptyNodes += 1
        }
        // params plus one big var if there are vars
        let neededEmptyNodes = numParams + if varDefs.len() > 0 { 1 } else { 0 };
        if neededEmptyNodes > emptyNodes {
            let num = neededEmptyNodes - emptyNodes;
            let empties: Vec<_> = iter::repeat(()).map(|_| makeEmpty()).take(num).collect();
            stats.splice(0..0, empties.into_iter());
        } else {
            let num = emptyNodes - neededEmptyNodes;
            stats.splice(0..num, iter::empty());
        }

        // add param coercions
        let mut next = 0;
        for param in params.iter() {
            let localty = self.locals.get(param).unwrap().ty;
            let coercion = makeAsmCoercion(makeName(param.clone()), localty);
            let stat = an!(Assign(true, makeName(param.clone()), coercion));
            stats[next] = an!(Stat(stat));
            next += 1;
        }
        if varDefs.len() > 0 {
            stats[next] = an!(Var(varDefs));
        }
        /*
        if (inlines->size() > 0) {
          var i = 0;
          traverse(func, function(node, type) {
            if (type == CALL && node[1][0] == NAME && node[1][1] == 'inlinejs') {
              node[1] = inlines[i++]; // swap back in the body
            }
          });
        }
        */

        // ensure that there's a final RETURN statement if needed.
        if let Some(ret) = self.ret {
            let hasret = stats.last().map_or(false, |st| st.isReturn());
            if !hasret {
                let zero = makeAsmCoercedZero(ret, self.floatZero.clone());
                stats.push(an!(Return(Some(zero))))
            }
        }

        //printErr('denormalized \n\n' + astToSrc(func) + '\n\n');
    }

    fn getType(&self, name: &IString) -> Option<AsmType> {
        self.locals.get(name).map(|l| l.ty)
    }
    // RSNOTE: sometimes we don't have access to the whole asmdata
    fn getTypeFromLocals(locals: &HashMap<IString, Local>, name: &IString) -> Option<AsmType> {
        locals.get(name).map(|l| l.ty)
    }
    fn setType(&mut self, name: IString, ty: AsmType) {
        self.locals.get_mut(&name).unwrap().ty = ty;
    }

    fn isLocal(&self, name: &IString) -> bool {
        self.locals.contains_key(name)
    }
    fn isParam(&self, name: &IString) -> bool {
        self.locals.get(name).map_or(false, |l| l.param)
    }
    fn isVar(&self, name: &IString) -> bool {
        self.locals.get(name).map_or(false, |l| !l.param)
    }

    fn addParam(&mut self, name: IString, ty: AsmType) {
        let prev = self.locals.insert(name.clone(), Local::new(ty, true));
        assert!(prev.is_none());
        self.params.push(name);
    }
    fn addVar(&mut self, name: IString, ty: AsmType) {
        let prev = self.locals.insert(name.clone(), Local::new(ty, false));
        assert!(prev.is_none());
        self.vars.push(name);
    }
    // RSNOTE: sometimes we don't have access to the whole asmdata
    fn addVarToLocalsAndVars(locals: &mut HashMap<IString, Local>, vars: &mut Vec<IString>, name: IString, ty: AsmType) {
        let prev = locals.insert(name.clone(), Local::new(ty, false));
        assert!(prev.is_none());
        vars.push(name);
    }

    fn deleteVar(&mut self, name: &IString) {
        self.locals.remove(name).unwrap();
        let pos = self.vars.iter().position(|v| v == name).unwrap();
        self.vars.remove(pos);
    }
}

struct HeapInfo {
    unsign: bool,
    floaty: bool,
    bits: u32,
    ty: AsmType,
}

enum AsmSign {
  Flexible, // small constants can be signed or unsigned, variables are also flexible
  Signed,
  Unsigned,
  Nonsigned,
}

fn parseHeap(name_str: &str) -> Option<HeapInfo> {
    if &name_str[..4] != "HEAP" { return None }
    let name = name_str.as_bytes();
    let (unsign, floaty) = (name[4] == b'U', name[4] == b'F');
    let bit_ofs = if unsign || floaty { 5 } else { 4 };
    let bits = name_str[bit_ofs..].parse().unwrap();
    let ty = if !floaty {
        AsmType::Int
    } else if bits == 64 {
        AsmType::Double
    } else {
        AsmType::Float
    };
    Some(HeapInfo { unsign: unsign, floaty: floaty, bits: bits, ty: ty })
}

fn detectType(node: &AstValue, asmDataLocals: Option<&HashMap<IString, Local>>, asmFloatZero: &mut Option<IString>, inVarDef: bool) -> Option<AsmType> {
    match *node {
        Num(n) => {
            Some(if !isInteger(n) {
                AsmType::Double
            } else {
                AsmType::Int
            })
        },
        Name(ref name) => {
            if let Some(asmDataLocals) = asmDataLocals {
                let ret = AsmData::getTypeFromLocals(asmDataLocals, name);
                if ret.is_some() { return ret }
            }
            Some(if !inVarDef {
                match *name {
                    is!("inf") |
                    is!("nan") => AsmType::Double,
                    is!("tempRet0") => AsmType::Int,
                    _ => return None,
                }
            } else {
                // We are in a variable definition, where Math_fround(0) optimized into a global constant becomes f0 = Math_fround(0)
                let nodestr = name;
                if let Some(ref asmFloatZero) = *asmFloatZero {
                    assert!(asmFloatZero == nodestr)
                } else {
                    // RSTODO: asmFloatZero is currently per pass, but in emoptimizer it's per file
                    *asmFloatZero = Some(nodestr.clone())
                }
                AsmType::Float
            })
        },
        UnaryPrefix(ref op, ref right) => {
            // RSTODO: istring match? Are there any 2 char unary prefixes?
            match op.as_bytes()[0] {
                b'+' => Some(AsmType::Double),
                b'-' => detectType(right, asmDataLocals, asmFloatZero, inVarDef),
                b'!' |
                b'~' => Some(AsmType::Int),
                _ => None,
            }
        },
        Call(ref fnexpr, _) => {
            match **fnexpr {
                Name(ref name) => {
                    Some(match *name {
                        is!("Math_fround") => AsmType::Float,
                        is!("SIMD_Float32x4") |
                        is!("SIMD_Float32x4_check") => AsmType::Float32x4,
                        is!("SIMD_Float64x2") |
                        is!("SIMD_Float64x2_check") => AsmType::Float64x2,
                        is!("SIMD_Int8x16") |
                        is!("SIMD_Int8x16_check") => AsmType::Int8x16,
                        is!("SIMD_Int16x8") |
                        is!("SIMD_Int16x8_check") => AsmType::Int16x8,
                        is!("SIMD_Int32x4") |
                        is!("SIMD_Int32x4_check") => AsmType::Int32x4,
                        is!("SIMD_Bool8x16") |
                        is!("SIMD_Bool8x16_check") => AsmType::Bool8x16,
                        is!("SIMD_Bool16x8") |
                        is!("SIMD_Bool16x8_check") => AsmType::Bool16x8,
                        is!("SIMD_Bool32x4") |
                        is!("SIMD_Bool32x4_check") => AsmType::Bool32x4,
                        is!("SIMD_Bool64x2") |
                        is!("SIMD_Bool64x2_check") => AsmType::Bool64x2,
                        _ => return None,
                    })
                },
                _ => None,
            }
        },
        Conditional(_, ref iftrue, _) => {
            detectType(iftrue, asmDataLocals, asmFloatZero, inVarDef)
        },
        Binary(ref op, ref left, _) => {
            match op.as_bytes()[0] {
                b'+' | b'-' |
                b'*' | b'/' |
                b'%' => detectType(left, asmDataLocals, asmFloatZero, inVarDef),
                b'|' | b'&' | b'^' |
                b'<' | b'>' | // handles <<, >>, >>=, <=
                b'=' | b'!' => Some(AsmType::Int), // handles ==, !=
                _ => None,
            }
        },
        Seq(_, ref right) => detectType(right, asmDataLocals, asmFloatZero, inVarDef),
        Sub(ref target, _) => {
            let name = target.getName().0;
            Some(if let Some(info) = parseHeap(name) {
                // XXX ASM_FLOAT?
                if info.floaty { AsmType::Double } else { AsmType::Int }
            } else {
                return None
            })
        },
        _ => None,
    }
    //dump("horrible", node);
    //assert(0);
}

// RSTODO: is this used?
fn detectSign(node: &AstValue) -> AsmSign {
    match *node {
        Binary(ref op, _, _) => {
            let opch = op.as_bytes()[0];
            if opch == b'>' && *op == is!(">>>") {
                return AsmSign::Unsigned
            }
            match opch {
                b'|' | b'&' | b'^' |
                b'<' | b'>' |
                b'=' | b'!' => AsmSign::Signed,
                b'+' | b'-' => AsmSign::Flexible,
                b'*' | b'/' => AsmSign::Nonsigned,
                _ => panic!(),
            }
        },
        UnaryPrefix(ref op, _) => {
            // RSTODO: istring match? Are there any 2 char unary prefixes?
            match op.as_bytes()[0] {
                b'-' => AsmSign::Flexible,
                b'+' => AsmSign::Nonsigned,
                b'~' => AsmSign::Signed,
                _ => panic!(),
            }
        },
        Num(value) => {
            if value < 0f64 {
                AsmSign::Signed
            } else if !isInteger32(value) {
                AsmSign::Nonsigned
            } else if value <= i32::MAX as f64 {
                AsmSign::Flexible
            } else {
                AsmSign::Unsigned
            }
        },
        Name(_) => AsmSign::Flexible,
        Conditional(_, ref iftrue, _) => detectSign(iftrue),
        Call(mast!(Name(is!("Math_fround"))), _) => AsmSign::Nonsigned,
        _ => panic!(),
    }
}

//==================
// Infrastructure
//==================

fn getHeapStr(x: u32, unsign: bool) -> IString {
    match x {
        8 => if unsign { is!("HEAPU8") } else { is!("HEAP8") },
        16 => if unsign { is!("HEAPU16") } else { is!("HEAP16") },
        32 => if unsign { is!("HEAPU32") } else { is!("HEAP32") },
        _ => panic!(),
    }
}

fn deStat(node: &AstValue) -> &AstValue {
    if let Stat(ref stat) = *node { stat } else { node }
}
fn mutDeStat(node: &mut AstValue) -> &mut AstValue {
    if let Stat(ref mut stat) = *node { stat } else { node }
}
fn intoDeStat(node: AstNode) -> AstNode {
    if let Stat(stat) = *node { stat } else { node }
}

fn getStatements(node: &mut AstValue) -> Option<&mut AstVec<AstNode>> {
    Some(match *node {
        Defun(_, _, ref mut stats) => stats,
        Block(ref mut stats) if stats.len() > 0 => stats,
        _ => return None,
    })
}


// Constructions TODO: share common constructions, and assert they remain frozen
// RSTODO: remove all constructions and replace with an!()?

fn makeArray<T>(size_hint: usize) -> AstVec<T> {
    builder::makeTArray(size_hint)
}

// RSTODO: remove?
//fn makeBool(b: bool) -> Ref {
//    let mut r = ARENA.alloc();
//    r.setBool(b);
//    r
//}

// RSTODO: remove?
//fn makeString(s: IString) -> Ref {
//    let mut r = ARENA.alloc();
//    r.setIString(s);
//    r
//}

fn makeEmpty() -> AstNode {
    builder::makeToplevel()
}

fn makeNum(x: f64) -> AstNode {
    builder::makeDouble(x)
}

fn makeName(str: IString) -> AstNode {
    builder::makeName(str)
}

fn makeBlock() -> AstNode {
    builder::makeBlock()
}

// RSTODO: remove?
//fn make1(s1: IString, a: Ref) -> Ref {
//    let mut r = makeArray(2);
//    r
//        .push_back(makeString(s1))
//        .push_back(a);
//    r
//}

// RSTODO: remove?
//fn make2IString(s1: IString, s2: IString, a: Ref) -> Ref {
//    let mut r = makeArray(3);
//    r
//        .push_back(makeString(s1))
//        .push_back(makeString(s2))
//        .push_back(a);
//    r
//}
//
//fn make2Ref(s1: IString, a: Ref, b: Ref) -> Ref {
//    let mut r = makeArray(3);
//    r
//        .push_back(makeString(s1))
//        .push_back(a)
//        .push_back(b);
//    r
//}

// RSTODO: remove?
//fn make3IString(ty: IString, a: IString, b: Ref, c: Ref) -> Ref {
//    let mut r = makeArray(4);
//    r
//        .push_back(makeString(ty))
//        .push_back(makeString(a))
//        .push_back(b)
//        .push_back(c);
//    r
//}
//
//fn make3Ref(ty: IString, a: Ref, b: Ref, c: Ref) -> Ref {
//    let mut r = makeArray(4);
//    r
//        .push_back(makeString(ty))
//        .push_back(a)
//        .push_back(b)
//        .push_back(c);
//    r
//}

// RSTODO: could be massively shortened by keeping a mapping from type to
// istring method+number of zeros, and just using that? Would also benefit
// method below
fn makeAsmCoercedZero(ty: AsmType, asmFloatZero: Option<IString>) -> AstNode {
    fn zarr(n: usize) -> AstVec<AstNode> {
        let mut arr = makeArray(n);
        for _ in 0..n { arr.push(makeNum(0f64)); }
        arr
    }
    match ty {
        AsmType::Int => makeNum(0f64),
        AsmType::Double => an!(UnaryPrefix(is!("+"), makeNum(0f64))),
        AsmType::Float => {
            if let Some(f0) = asmFloatZero {
                makeName(f0)
            } else {
                an!(Call(makeName(is!("Math_fround")), zarr(1)))
            }
        },
        AsmType::Float32x4 => {
            an!(Call(makeName(is!("SIMD_Float32x4")), zarr(4)))
        },
        AsmType::Float64x2 => {
            an!(Call(makeName(is!("SIMD_Float64x2")), zarr(2)))
        },
        AsmType::Int8x16 => {
            an!(Call(makeName(is!("SIMD_Int8x16")), zarr(16)))
        },
        AsmType::Int16x8 => {
            an!(Call(makeName(is!("SIMD_Int16x8")), zarr(8)))
        },
        AsmType::Int32x4 => {
            an!(Call(makeName(is!("SIMD_Int32x4")), zarr(4)))
        },
        AsmType::Bool8x16 => {
            an!(Call(makeName(is!("SIMD_Bool8x16")), zarr(16)))
        },
        AsmType::Bool16x8 => {
            an!(Call(makeName(is!("SIMD_Bool16x8")), zarr(8)))
        },
        AsmType::Bool32x4 => {
            an!(Call(makeName(is!("SIMD_Bool32x4")), zarr(4)))
        },
        AsmType::Bool64x2 => {
            an!(Call(makeName(is!("SIMD_Bool64x2")), zarr(2)))
        },
    }
}

fn makeAsmCoercion(node: AstNode, ty: AsmType) -> AstNode {
    fn arr(n: AstNode) -> AstVec<AstNode> {
        let mut arr = makeArray(1);
        arr.push(n);
        arr
    }
    match ty {
        AsmType::Int => an!(Binary(is!("|"), node, makeNum(0f64))),
        AsmType::Double => an!(UnaryPrefix(is!("+"), node)),
        AsmType::Float => an!(Call(makeName(is!("Math_fround")), arr(node))),
        AsmType::Float32x4 => an!(Call(makeName(is!("SIMD_Float32x4_check")), arr(node))),
        AsmType::Float64x2 => an!(Call(makeName(is!("SIMD_Float64x2_check")), arr(node))),
        AsmType::Int8x16 => an!(Call(makeName(is!("SIMD_Int8x16_check")), arr(node))),
        AsmType::Int16x8 => an!(Call(makeName(is!("SIMD_Int16x8_check")), arr(node))),
        AsmType::Int32x4 => an!(Call(makeName(is!("SIMD_Int32x4_check")), arr(node))),
        // non-validating code, emit nothing XXX this is dangerous, we should only allow this when we know we are not validating
        AsmType::Bool8x16 |
        AsmType::Bool16x8 |
        AsmType::Bool32x4 |
        AsmType::Bool64x2 => node,
    }
}

// Checks

fn isEmpty(node: &AstValue) -> bool {
    match *node {
        Toplevel(ref stats) |
        Block(ref stats) if stats.is_empty() => true,
        _ => false,
    }
}

fn commable(node: &AstValue) -> bool { // TODO: hashing
    match *node {
        Assign(..) |
        Binary(..) |
        UnaryPrefix(..) |
        Name(..) |
        Num(..) |
        Call(..) |
        Seq(..) |
        Conditional(..) |
        Sub(..) => true,
        _ => false,
    }
}

fn isMathFunc(name: &str) -> bool {
    name.starts_with("Math_")
}

fn callHasSideEffects(node: &AstValue) -> bool { // checks if the call itself (not the args) has side effects (or is not statically known)
    let (fname, _) = node.getCall();
    if let Name(ref name) = **fname { !isMathFunc(name) } else { true }
}

// RSTODO: just run hasSideEffects on all children?
fn hasSideEffects(node: &AstValue) -> bool { // this is 99% incomplete!
    match *node {
        Num(_) |
        Name(_) |
        Str(_) => false,

        Binary(_, ref left, ref right) => hasSideEffects(left) || hasSideEffects(right),
        Call(_, ref args) => {
            if callHasSideEffects(node) { return true }
            for arg in args.iter() {
                if hasSideEffects(arg) { return true }
            }
            false
        },
        Conditional(ref cond, ref iftrue, ref iffalse) => hasSideEffects(cond) || hasSideEffects(iftrue) || hasSideEffects(iffalse),
        Sub(ref target, ref index) => hasSideEffects(target) || hasSideEffects(index),
        UnaryPrefix(_, ref right) => hasSideEffects(right),

        // RSTODO: implement these?
        Array(..) |
        Assign(..) |
        Block(..) |
        Break(..) |
        Continue(..) |
        Defun(..) |
        Do(..) |
        Dot(..) |
        If(..) |
        Label(..) |
        New(..) |
        Object(..) |
        Return(..) |
        Seq(..) |
        Stat(..) |
        Switch(..) |
        Toplevel(..) |
        Var(..) |
        While(..) => true,
    }
}

// checks if a node has just basic operations, nothing with side effects nor that can notice side effects, which
// implies we can move it around in the code
fn triviallySafeToMove(node: &AstValue, asmDataLocals: &HashMap<IString, Local>) -> bool {
    let mut ok = true;
    traversePre(node, |node: &AstValue| {
        // RSTODO: faster to early return this closure if ok is already false?
        match *node {
            Stat(..) |
            Binary(..) |
            UnaryPrefix(..) |
            Assign(..) |
            Num(..) => (),
            Name(ref name) => if !asmDataLocals.contains_key(name) { ok = false },
            Call(_, _) => if callHasSideEffects(node) { ok = false },
            _ => ok = false,
        }
    });
    ok
}
//bool triviallySafeToMove(Ref node, AsmData& asmData) {
//  bool ok = true;
//  traversePre(node, [&](Ref node) {
//    Ref type = node[0];
//    if (type == STAT || type == BINARY || type == UNARY_PREFIX || type == ASSIGN || type == NUM) return;
//    else if (type == NAME) {
//      if (!asmData.isLocal(node[1]->getIString())) ok = false;
//    } else if (type == CALL) {
//      if (callHasSideEffects(node)) ok = false;
//    } else {
//      ok = false;
//    }  
//  });
//  return ok;
//}

// Transforms

// We often have branchings that are simplified so one end vanishes, and
// we then get
//   if (!(x < 5))
// or such. Simplifying these saves space and time.
fn simplifyNotCompsDirect(node: &mut AstValue, asmFloatZero: &mut Option<IString>) {
    // de-morgan's laws do not work on floats, due to nans >:(
    let newvalue = {
        let mut inner = if let UnaryPrefix(is!("!"), ref mut i) = *node { i } else { return };
        let oldpos = match **inner {
            ref mut bin @ Binary(..) => {
                {
                // RSTODO: no way to capture whole expression as well as subexpressions?
                let (op, left, right) = bin.getMutBinary();
                if !(detectType(left, None, asmFloatZero, false) == Some(AsmType::Int) &&
                     detectType(right, None, asmFloatZero, false) == Some(AsmType::Int)) { return }
                match *op {
                    is!("<") => *op = is!(">="),
                    is!("<=") => *op = is!(">"),
                    is!(">") => *op = is!("<="),
                    is!(">=") => *op = is!("<"),
                    is!("==") => *op = is!("!="),
                    is!("!=") => *op = is!("=="),
                    _ => return
                }
                }
                bin
            }
            UnaryPrefix(is!("!"), ref mut right) => right,
            _ => return,
        };
        mem::replace(oldpos, *makeEmpty())
    };
    *node = newvalue
}

fn flipCondition(cond: &mut AstValue, asmFloatZero: &mut Option<IString>) {
    let mut newcond = makeEmpty();
    mem::swap(cond, &mut newcond);
    newcond = an!(UnaryPrefix(is!("!"), newcond));
    mem::swap(cond, &mut newcond);
    simplifyNotCompsDirect(cond, asmFloatZero);
}

// RSTODO
// RSNOTE: probably don't want to implement this as it causes deliberate
// memory leaks
//void safeCopy(Ref target, Ref source) { // safely copy source onto target, even if source is a subnode of target
//  Ref temp = source; // hold on to source
//  *target = *temp;
//}

fn clearEmptyNodes(arr: &mut AstVec<AstNode>) {
    arr.retain(|an: &AstNode| { !isEmpty(deStat(an)) })
}
// RSTODO
//void clearUselessNodes(Ref arr) {
//  int skip = 0;
//  for (size_t i = 0; i < arr->size(); i++) {
//    Ref curr = arr[i];
//    if (skip) {
//      arr[i-skip] = curr;
//    }
//    if (isEmpty(deStat(curr)) || (curr[0] == STAT && !hasSideEffects(curr[1]))) {
//      skip++;
//    }
//  }
//  if (skip) arr->setSize(arr->size() - skip);
//}

fn removeAllEmptySubNodes(ast: &mut AstValue) {
    traversePreMut(ast, |node: &mut AstValue| {
        match *node {
            Defun(_, _, ref mut stats) |
            Block(ref mut stats) => {
                clearEmptyNodes(stats)
            },
            Seq(_, _) => {
                // RSTODO: what about right being empty?
                let maybenewnode = {
                    let (left, right) = node.getMutSeq();
                    if isEmpty(left) {
                        Some(mem::replace(right, makeEmpty()))
                    } else {
                        None
                    }
                };
                if let Some(newnode) = maybenewnode {
                    *node = *newnode
                }
            },
            _ => (),
        }
    })
}
// RSTODO
//void removeAllUselessSubNodes(Ref ast) {
//  traversePrePost(ast, [](Ref node) {
//    Ref type = node[0];
//    if (type == DEFUN) {
//      clearUselessNodes(node[3]);
//    } else if (type == BLOCK && node->size() > 1 && !!node[1]) {
//      clearUselessNodes(node[1]);
//    } else if (type == SEQ && isEmpty(node[1])) {
//      safeCopy(node, node[2]);
//    }
//  }, [](Ref node) {
//    Ref type = node[0];
//    if (type == IF) {
//      bool empty2 = isEmpty(node[2]), has3 = node->size() == 4 && !!node[3], empty3 = !has3 || isEmpty(node[3]);
//      if (!empty2 && empty3 && has3) { // empty else clauses
//        node->setSize(3);
//      } else if (empty2 && !empty3) { // empty if blocks
//        safeCopy(node, make2(IF, make2(UNARY_PREFIX, L_NOT, node[1]), node[3]));
//      } else if (empty2 && empty3) {
//        if (hasSideEffects(node[1])) {
//          safeCopy(node, make1(STAT, node[1]));
//        } else {
//          safeCopy(node, makeEmpty());
//        }
//      }
//    }
//  });
//}
//
//Ref unVarify(Ref vars) { // transform var x=1, y=2 etc. into (x=1, y=2), i.e., the same assigns, but without a var definition
//  Ref ret = makeArray(1);
//  ret->push_back(makeString(STAT));
//  if (vars->size() == 1) {
//    ret->push_back(make3(ASSIGN, makeBool(true), makeName(vars[0][0]->getIString()), vars[0][1]));
//  } else {
//    ret->push_back(makeArray(vars->size()-1));
//    Ref curr = ret[1];
//    for (size_t i = 0; i+1 < vars->size(); i++) {
//      curr->push_back(makeString(SEQ));
//      curr->push_back(make3(ASSIGN, makeBool(true), makeName(vars[i][0]->getIString()), vars[i][1]));
//      if (i != vars->size()-2) {
//        curr->push_back(makeArray());
//        curr = curr[2];
//      }
//    }
//    curr->push_back(make3(ASSIGN, makeBool(true), makeName(vars->back()[0]->getIString()), vars->back()[1]));
//  }
//  return ret;
//}

// Calculations

fn measureCost(ast: &AstValue) -> isize {
    let mut size = 0isize;
    traversePre(ast, |node: &AstValue| {
        size += match *node {
            Num(_) |
            UnaryPrefix(_, _) => -1,
            Binary(_, _, mast!(Num(0f64))) => -1,
            Binary(is!("/"), _, _) |
            Binary(is!("%"), _, _) => 2,
            // RSTODO: call subtracts cost?
            Call(_, _) if !callHasSideEffects(node) => -2,
            Sub(_, _) => 1,
            _ => 0,
        };
        // RSTODO: the emoptimizer traversals actually traverse over arrays,
        // so the below nodes are given additional weight - not sure if this
        // is intentional or not, so we just simulate it. However, measureCost
        // is only ever called on an expression so some of relevant nodes
        // shouldn't be possible.
        size += match *node {
            Array(_) |
            Call(_, _) |
            Object(_) => 1,
            Block(_) |
            Defun(_, _, _) |
            Switch(_, _) |
            Toplevel(_) |
            Var(_) => panic!(),
            _ => 0,
        };
        size += 1
    });
    size
}

//=====================
// Optimization passes
//=====================

// RSTODO
//#define HASES \
//  bool has(const IString& str) { \
//    return count(str) > 0; \
//  } \
//  bool has(Ref node) { \
//    return node->isString() && count(node->getIString()) > 0; \
//  }
//
//class StringSet : public cashew::IStringSet {
//public:
//  StringSet() {}
//  StringSet(const char *str) : IStringSet(str) {}
//
//  HASES
//
//  void dump() {
//    err("===");
//    for (auto str : *this) {
//      errv("%s", str.c_str());
//    }
//    err("===");
//  }
//};

lazy_static! {
    static ref USEFUL_BINARY_OPS: phf::Set<IString> = iss![
        "<<",
        ">>",
        "|",
        "&",
        "^",
    ];
    static ref COMPARE_OPS: phf::Set<IString> = iss![
        "<",
        "<=",
        ">",
        ">=",
        "==",
        // RSTODO: should be ===?
        //"==",
        "!=",
        // RSTODO: present in emoptimizer, but don't think necessary?
        //"!==",
    ];
    static ref BITWISE: phf::Set<IString> = iss![
        "|",
        "&",
        "^",
    ];
    // division is unsafe as it creates non-ints in JS; mod is unsafe as signs matter so we can't remove |0's; mul does not nest with +,- in asm
    static ref SAFE_BINARY_OPS: phf::Set<IString> = iss![
        "+",
        "-",
    ];
    // binary ops that in asm must be coerced
    static ref COERCION_REQUIRING_BINARIES: phf::Set<IString> = iss![
        "*",
        "/",
        "%",
    ];
}

lazy_static! {
    static ref ASSOCIATIVE_BINARIES: phf::Set<IString> = iss![
        "+",
        "*",
        "|",
        "&",
        "^",
   ];
// RSTODO
//          CONTROL_FLOW("do while for if switch"),
//          LOOP("do while for"),
//          CONDITION_CHECKERS("if do while switch"),
//          SAFE_TO_DROP_COERCION("unary-prefix name num");
}

// RSTODO
//StringSet BREAK_CAPTURERS("do while for switch"),
//          CONTINUE_CAPTURERS("do while for"),
//          FUNCTIONS_THAT_ALWAYS_THROW("abort ___resumeException ___cxa_throw ___cxa_rethrow");

fn isFunctionTable(name: &str) -> bool {
    name.starts_with("FUNCTION_TABLE")
}

// RSTODO
//// Internal utilities
//
//bool canDropCoercion(Ref node) {
//  if (SAFE_TO_DROP_COERCION.has(node[0])) return true;
//  if (node[0] == BINARY) {
//    switch (node[1]->getCString()[0]) {
//      case '>': return node[1] == RSHIFT || node[1] == TRSHIFT;
//      case '<': return node[1] == LSHIFT;
//      case '|': case '^': case '&': return true;
//    }
//  }
//  return false;
//}
//
//Ref simplifyCondition(Ref node) {
//  node = simplifyNotCompsDirect(node);
//  // on integers, if (x == 0) is the same as if (x), and if (x != 0) as if (!x)
//  if (node[0] == BINARY && (node[1] == EQ || node[1] == NE)) {
//    Ref target;
//    if (detectType(node[2]) == ASM_INT && node[3][0] == NUM && node[3][1]->getNumber() == 0) {
//      target = node[2];
//    } else if (detectType(node[3]) == ASM_INT && node[2][0] == NUM && node[2][1]->getNumber() == 0) {
//      target = node[3];
//    }
//    if (!!target) {
//      if (target[0] == BINARY && (target[1] == OR || target[1] == TRSHIFT) && target[3][0] == NUM && target[3][1]->getNumber() == 0 &&
//          canDropCoercion(target[2])) {
//        target = target[2]; // drop the coercion, in a condition it is ok to do if (x)
//      }
//      if (node[1] == EQ) {
//        return make2(UNARY_PREFIX, L_NOT, target);
//      } else {
//        return target;
//      }
//    }
//  }
//  return node;
//}

// Passes

// Eliminator aka Expressionizer
//
// The goal of this pass is to eliminate unneeded variables (which represent one of the infinite registers in the LLVM
// model) and thus to generate complex expressions where possible, for example
//
//  var x = a(10);
//  var y = HEAP[20];
//  print(x+y);
//
// can be transformed into
//
//  print(a(10)+HEAP[20]);
//
// The basic principle is to scan along the code in the order of parsing/execution, and keep a list of tracked
// variables that are current contenders for elimination. We must untrack when we see something that we cannot
// cross, for example, a write to memory means we must invalidate variables that depend on reading from
// memory, since if we change the order then we do not preserve the computation.
//
// We rely on some assumptions about emscripten-generated code here, which means we can do a lot more than
// a general JS optimization can. For example, we assume that SUB nodes (indexing like HEAP[..]) are
// memory accesses or FUNCTION_TABLE accesses, and in both cases that the symbol cannot be replaced although
// the contents can. So we assume FUNCTION_TABLE might have its contents changed but not be pointed to
// a different object, which allows
//
//  var x = f();
//  FUNCTION_TABLE[x]();
//
// to be optimized (f could replace FUNCTION_TABLE, so in general JS eliminating x is not valid).
//
// In memSafe mode, we are more careful and assume functions can replace HEAP and FUNCTION_TABLE, which
// can happen in ALLOW_MEMORY_GROWTH mode

lazy_static! {
    static ref HEAP_NAMES: phf::Set<IString> = iss![
        "HEAP8",
        "HEAP16",
        "HEAP32",
        "HEAPU8",
        "HEAPU16",
        "HEAPU32",
        "HEAPF32",
        "HEAPF64",
   ];
}

fn isTempDoublePtrAccess(node: &AstValue) -> bool { // these are used in bitcasts; they are not really affecting memory, and should cause no invalidation
    assert!(node.isSub());
    // RSTODO: second arm in if-let https://github.com/rust-lang/rfcs/issues/935#issuecomment-213800427?
    if let Sub(_, mast!(Name(is!("tempDoublePtr")))) = *node { return true }
    if let Sub(_, mast!(Binary(_, Name(is!("tempDoublePtr")), _))) = *node { return true }
    if let Sub(_, mast!(Binary(_, _, Name(is!("tempDoublePtr"))))) = *node { return true }
    false
}

// RSTODO
//class StringIntMap : public std::unordered_map<IString, int> {
//public:
//  HASES
//};
//
//class StringStringMap : public std::unordered_map<IString, IString> {
//public:
//  HASES
//};
//
//class StringRefMap : public std::unordered_map<IString, Ref> {
//public:
//  HASES
//};
//
//class StringTypeMap : public std::unordered_map<IString, AsmType> {
//public:
//  HASES
//};

pub fn eliminate(ast: &mut AstValue, memSafe: bool) {
    #[cfg(feature = "profiling")]
    let (mut tasmdata, mut tfnexamine, mut tvarcheck, mut tstmtelim, mut tstmtscan, mut tcleanvars, mut treconstruct) = (Duration::new(0, 0), Duration::new(0, 0), Duration::new(0, 0), Duration::new(0, 0), Duration::new(0, 0), Duration::new(0, 0), Duration::new(0, 0));

    let mut asmFloatZero = None;

    // Find variables that have a single use, and if they can be eliminated, do so

    traverseFunctionsMut(ast, |func: &mut AstValue| {

    #[cfg(feature = "profiling")]
    let mut start = SystemTime::now();

    let mut asmData = AsmData::new(func);

    let mut varsToRemove;

    {
    let asmDataLocals = &mut asmData.locals;
    let asmDataVars = &mut asmData.vars;

    #[cfg(feature = "profiling")]
    {
    tasmdata += start.elapsed().unwrap();
    start = SystemTime::now();
    }

    // First, find the potentially eliminatable functions: that have one definition and one use
    // RSTODO: should some of these be usize?
    let mut definitions = HashMap::<IString, isize>::new();
    let mut namings = HashMap::<IString, isize>::new();
    let mut uses = HashMap::<IString, isize>::new();
    let mut potentials = HashSet::<IString>::new(); // local variables with 1 definition and 1 use
    let mut sideEffectFree = HashSet::<IString>::new(); // whether a local variable has no side effects in its definition. Only relevant when there are no uses
    let mut values = HashMap::<IString, *mut AstValue>::new();
    // variables being removed, that we can eliminate all 'var x;' of (this refers to VAR nodes we should remove)
    // 1 means we should remove it, 2 means we successfully removed it
    // RSTODO: use enum rather than isize
    varsToRemove = HashMap::<IString, isize>::new();
    let mut varsToTryToRemove = HashSet::<IString>::new(); // variables that have 0 uses, but have side effects - when we scan we can try to remove them

    // examine body and note locals
    traversePreMut(asmData.func, |node: &mut AstValue| {
        match *node {
            Name(ref name) => {
                *uses.entry(name.clone()).or_insert(0) += 1;
                *namings.entry(name.clone()).or_insert(0) += 1;
            },
            Assign(_, mast!(Name(ref name)), ref mut value) => {
                // values is only used if definitions is 1
                let entry = definitions.entry(name.clone()).or_insert(0);
                *entry += 1;
                if *entry == 1 {
                    let prev = values.insert(name.clone(), &mut **value as *mut _);
                    assert!(prev.is_none());
                }
                // because the name node will show up by itself in the previous case
                *uses.entry(name.clone()).or_insert(0) -= 1;
            },
            _ => (),
        }
    });

    #[cfg(feature = "profiling")]
    {
    tfnexamine += start.elapsed().unwrap();
    start = SystemTime::now();
    }

    {
    fn unprocessVariable(name: &IString, potentials: &mut HashSet<IString>, sideEffectFree: &mut HashSet<IString>, varsToRemove: &mut HashMap<IString, isize>, varsToTryToRemove: &mut HashSet<IString>) {
        // RSNOTE: all of these may not be present
        potentials.remove(name);
        sideEffectFree.remove(name);
        varsToRemove.remove(name);
        varsToTryToRemove.remove(name);
    }
    fn processVariable(name: &IString, asmDataLocals: &HashMap<IString, Local>, definitions: &mut HashMap<IString, isize>, potentials: &mut HashSet<IString>, sideEffectFree: &mut HashSet<IString>, uses: &mut HashMap<IString, isize>, values: &HashMap<IString, *mut AstValue>, varsToRemove: &mut HashMap<IString, isize>, varsToTryToRemove: &mut HashSet<IString>) {
        // RSNOTE: names that only appear in var statements won't have been inserted above, do them now
        let numdefs = *definitions.get(name).unwrap_or(&0);
        let numuses = *uses.get(name).unwrap_or(&0);
        if numdefs == 1 && numuses == 1 {
            // RSNOTE: could be present already if var A has been eliminated which cascades
            // to var B, and then var B gets processed again when iterating over the locals
            potentials.insert(name.clone());
        } else if numuses == 0 && numdefs <= 1 { // no uses, no def or 1 def (cannot operate on phis, and the llvm optimizer will remove unneeded phis anyhow) (no definition means it is a function parameter, or a local with just |var x;| but no defining assignment
            let val = unsafe { values.get(name).map(|v| &mut **v) };
            let sideEffects = match val {
                // First, pattern-match
                //  (HEAP32[((tempDoublePtr)>>2)]=((HEAP32[(($_sroa_0_0__idx1)>>2)])|0),HEAP32[(((tempDoublePtr)+(4))>>2)]=((HEAP32[((($_sroa_0_0__idx1)+(4))>>2)])|0),(+(HEAPF64[(tempDoublePtr)>>3])))
                // which has no side effects and is the special form of converting double to i64.
                // RSTODO: how does this differ to the check for isTempDoublePtrAccess below? Duplicate?
                Some(&mut Seq(mast!(Assign(_, Sub(_, Binary(is!(">>"), Name(is!("tempDoublePtr")), _)), _)), _)) => false,
                // If not that, then traverse and scan normally.
                Some(ref value) => hasSideEffects(value),
                None => false,
            };
            if !sideEffects {
                // RSNOTE: could be present already if var A has been eliminated which cascades
                // to var B, and then var B gets processed again when iterating over the locals
                let newremoveval = if numdefs == 0 { 2 } else { 1 };
                let prev = varsToRemove.insert(name.clone(), newremoveval); // remove it normally
                assert!(prev.is_none() || prev.unwrap() == newremoveval);
                sideEffectFree.insert(name.clone());
                // Each time we remove a variable with 0 uses, if its value has no
                // side effects and vanishes too, then we can remove a use from variables
                // appearing in it, and possibly eliminate again
                if let Some(value) = val {
                    traversePreMut(value, |node: &mut AstValue| {
                        match *node {
                            Name(ref mut name_) => {
                                let name = &name_.clone();
                                *name_ = is!(""); // we can remove this - it will never be shown, and should not be left to confuse us as we traverse
                                // RSNOTE: e.g. removing sp
                                if asmDataLocals.contains_key(name) {
                                    {
                                    let numuses = uses.get_mut(name).unwrap();
                                    *numuses -= 1; // cannot be infinite recursion since we descend an energy function
                                    assert!(*numuses >= 0);
                                    }
                                    unprocessVariable(name, potentials, sideEffectFree, varsToRemove, varsToTryToRemove);
                                    processVariable(name, asmDataLocals, definitions, potentials, sideEffectFree, uses, values, varsToRemove, varsToTryToRemove);
                                }
                            },
                            // no side effects, so this must be a Math.* call or such. We can just ignore it and all children
                            Call(_, _) => *node = Name(is!("")),
                            _ => (),
                        }
                    })
                }
            }
        }
    }
    for name in asmDataLocals.keys() {
        processVariable(name, asmDataLocals, &mut definitions, &mut potentials, &mut sideEffectFree, &mut uses, &values, &mut varsToRemove, &mut varsToTryToRemove);
    }
    }

    #[cfg(feature = "profiling")]
    {
    tvarcheck += start.elapsed().unwrap();
    start = SystemTime::now();
    }

    //printErr('defs: ' + JSON.stringify(definitions));
    //printErr('uses: ' + JSON.stringify(uses));
    //printErr('values: ' + JSON.stringify(values));
    //printErr('locals: ' + JSON.stringify(locals));
    //printErr('varsToRemove: ' + JSON.stringify(varsToRemove));
    //printErr('varsToTryToRemove: ' + JSON.stringify(varsToTryToRemove));
    drop(values);
    //printErr('potentials: ' + JSON.stringify(potentials));
    // We can now proceed through the function. In each list of statements, we try to eliminate
    #[derive(Debug)]
    struct Tracking {
        usesGlobals: bool,
        usesMemory: bool,
        hasDeps: bool,
        defNode: *mut AstValue,
        doesCall: bool,
    }
    let mut tracked = HashMap::<IString, Tracking>::new();
    // #define dumpTracked() { errv("tracking %d", tracked.size()); for (auto t : tracked) errv("... %s", t.first.c_str()); }
    // Although a set would be more appropriate, it would also be slower
    let mut depMap = HashMap::<IString, Vec<IString>>::new();

    let mut globalsInvalidated = false; // do not repeat invalidations, until we track something new
    let mut memoryInvalidated = false;
    let mut callsInvalidated = false;

    fn track(name: IString, value: &AstValue, defNode: *mut AstValue, asmDataLocals: &HashMap<IString, Local>, potentials: &HashSet<IString>, depMap: &mut HashMap<IString, Vec<IString>>, tracked: &mut HashMap<IString, Tracking>, globalsInvalidated: &mut bool, memoryInvalidated: &mut bool, callsInvalidated: &mut bool) { // add a potential that has just been defined to the tracked list, we hope to eliminate it
        let mut track = Tracking {
            usesGlobals: false,
            usesMemory: false,
            hasDeps: false,
            defNode: defNode,
            doesCall: false,
        };
        let mut ignoreName = false; // one-time ignorings of names, as first op in sub and call
        traversePre(value, |node: &AstValue| {
            match *node {
                Name(ref depName) => {
                    if !ignoreName {
                        if !asmDataLocals.contains_key(depName) {
                            track.usesGlobals = true
                        }
                        if !potentials.contains(depName) { // deps do not matter for potentials - they are defined once, so no complexity
                            depMap.entry(depName.clone()).or_insert_with(Vec::new).push(name.clone());
                            track.hasDeps = true
                        }
                    } else {
                        ignoreName = false
                    }
                },
                Sub(..) => {
                    track.usesMemory = true;
                    ignoreName = true
                },
                Call(..) => {
                    track.usesGlobals = true;
                    track.usesMemory = true;
                    track.doesCall = true;
                    ignoreName = true
                },
                _ => {
                    ignoreName = false
                },
            }
        });
        if track.usesGlobals { *globalsInvalidated = false }
        if track.usesMemory { *memoryInvalidated = false }
        if track.doesCall { *callsInvalidated = false }
        let prev = tracked.insert(name, track);
        // RSTODO: valid assertion?
        assert!(prev.is_none());
    };

    // TODO: invalidate using a sequence number for each type (if you were tracked before the last invalidation, you are cancelled). remove for.in loops
    fn invalidateGlobals(tracked: &mut HashMap<IString, Tracking>) {
        let temp: Vec<_> = tracked.iter().filter(|&(_, info)| info.usesGlobals).map(|(k, _)| k.clone()).collect();
        for name in temp { tracked.remove(&name).unwrap(); }
    }
    fn invalidateMemory(tracked: &mut HashMap<IString, Tracking>) {
        let temp: Vec<_> = tracked.iter().filter(|&(_, info)| info.usesMemory).map(|(k, _)| k.clone()).collect();
        for name in temp { tracked.remove(&name).unwrap(); }
    }
    fn invalidateCalls(tracked: &mut HashMap<IString, Tracking>) {
        let temp: Vec<_> = tracked.iter().filter(|&(_, info)| info.doesCall).map(|(k, _)| k.clone()).collect();
        for name in temp { tracked.remove(&name).unwrap(); }
    }

    fn invalidateByDep(dep: &IString, depMap: &mut HashMap<IString, Vec<IString>>, tracked: &mut HashMap<IString, Tracking>) {
        if let Some(deps) = depMap.remove(dep) {
            for name in deps {
                // RSNOTE: deps may not currently be in tracked
                tracked.remove(&name);
            }
        }
    }

    {
    // Generate the sequence of execution. This determines what is executed before what, so we know what can be reordered. Using
    // that, performs invalidations and eliminations
    let mut scan = |node: &mut AstValue, asmDataLocals: &HashMap<IString, Local>, tracked: &mut HashMap<IString, Tracking>| {
        let mut abort = false;
        let mut allowTracking = true; // false inside an if; also prevents recursing in an if
        // RSTODO: rather than these all being params why not pass a reference to a single struct that looks up necessary data?
        // RSTODO: note that this cannot be a closure because it's recursive
        // RSTODO: maybe get rid of functions entirely and turn it into a loop with manual tracking of the state stack?
        fn traverseInOrder(node: &mut AstValue, ignoreSub: bool, memSafe: bool, asmDataLocals: &HashMap<IString, Local>, uses: &HashMap<IString, isize>, potentials: &HashSet<IString>, sideEffectFree: &HashSet<IString>, varsToRemove: &mut HashMap<IString, isize>, varsToTryToRemove: &HashSet<IString>, depMap: &mut HashMap<IString, Vec<IString>>, tracked: &mut HashMap<IString, Tracking>, globalsInvalidated: &mut bool, memoryInvalidated: &mut bool, callsInvalidated: &mut bool, abort: &mut bool, allowTracking: &mut bool) {
            macro_rules! traverseInOrder {
                ($( $arg:expr ),*) => {
                    traverseInOrder($( $arg ),+, memSafe, asmDataLocals, uses, potentials, sideEffectFree, varsToRemove, varsToTryToRemove, depMap, tracked, globalsInvalidated, memoryInvalidated, callsInvalidated, abort, allowTracking)
                };
            }
            if *abort { return }
            let nodeptr = node as *mut _;
            match *node {
                Assign(_, ref mut target, ref mut value) => {
                    // If this is an assign to a name, handle it below rather than
                    // traversing and treating as a read
                    if !target.isName() {
                        traverseInOrder!(target, true) // evaluate left
                    }
                    traverseInOrder!(value, false); // evaluate right
                    let targetName = if let mast!(Name(ref name)) = *target { Some(name.clone()) } else { None };
                    // do the actual assignment
                    // RSTODO: perhaps some of these conditions could be simplified, but what we'd actually like to do is fix it so
                    // that track doesn't need to take a pointer
                    if let Some(name) = targetName {
                        if potentials.contains(&name) && *allowTracking {
                            track(name, value, nodeptr, asmDataLocals, potentials, depMap, tracked, globalsInvalidated, memoryInvalidated, callsInvalidated);
                        } else if varsToTryToRemove.contains(&name) {
                            // replace it in-place
                            let mut newnode = makeEmpty();
                            mem::swap(value, &mut newnode);
                            // RSTODO: unsafe because target and value are invalid after this, non-lexical lifetimes might fix
                            unsafe { mem::swap(&mut *nodeptr, &mut newnode) };
                            let prev = varsToRemove.insert(name, 2);
                            assert!(prev.is_none());
                        } else {
                            // expensive check for invalidating specific tracked vars. This list is generally quite short though, because of
                            // how we just eliminate in short spans and abort when control flow happens TODO: history numbers instead
                            invalidateByDep(&name, depMap, tracked); // can happen more than once per dep..
                            if !asmDataLocals.contains_key(&name) && !*globalsInvalidated {
                                invalidateGlobals(tracked);
                                *globalsInvalidated = true
                            }
                            // if we can track this name (that we assign into), and it has 0 uses and we want to remove its VAR
                            // definition - then remove it right now, there is no later chance
                            if *allowTracking && varsToRemove.contains_key(&name) && *uses.get(&name).unwrap() == 0 {
                                track(name.clone(), value, nodeptr, asmDataLocals, potentials, depMap, tracked, globalsInvalidated, memoryInvalidated, callsInvalidated);
                                doEliminate(&name, nodeptr, sideEffectFree, varsToRemove, tracked);
                            }
                        }
                    } else if target.isSub() {
                        if isTempDoublePtrAccess(target) {
                            if !*globalsInvalidated {
                                invalidateGlobals(tracked);
                                *globalsInvalidated = true
                            }
                        } else if !*memoryInvalidated {
                            invalidateMemory(tracked);
                            *memoryInvalidated = true
                        }
                    }
                },
                Sub(_, _) => {
                    {
                    let (target, index) = node.getMutSub();
                    // Only keep track of the global array names in memsafe mode i.e.
                    // when they may change underneath us due to resizing
                    if !target.isName() || memSafe {
                        traverseInOrder!(target, false) // evaluate inner
                    }
                    traverseInOrder!(index, false) // evaluate outer
                    }
                    // ignoreSub means we are a write (happening later), not a read
                    if !ignoreSub && !isTempDoublePtrAccess(node)
                            // do the memory access
                            && !*callsInvalidated {
                        invalidateCalls(tracked);
                        *callsInvalidated = true
                    }
                },
                Binary(ref op, ref mut left, ref mut right) => {
                    let mut flipped = false;
                    fn is_name_or_num(v: &AstValue) -> bool { v.isName() || v.isNum() }
                    if ASSOCIATIVE_BINARIES.contains(op) && !is_name_or_num(left) && is_name_or_num(right) { // TODO recurse here?
                        // associatives like + and * can be reordered in the simple case of one of the sides being a name, since we assume they are all just numbers
                        mem::swap(left, right);
                        flipped = true
                    }
                    traverseInOrder!(left, false);
                    traverseInOrder!(right, false);
                    if flipped && is_name_or_num(left) { // dunno if we optimized, but safe to flip back - and keeps the code closer to the original and more readable
                        mem::swap(left, right);
                    }
                },
                Name(ref name) => {
                    if tracked.contains_key(name) {
                        doEliminate(name, nodeptr, sideEffectFree, varsToRemove, tracked);
                    } else if !asmDataLocals.contains_key(name) && !*callsInvalidated && (memSafe || !HEAP_NAMES.contains(name)) { // ignore HEAP8 etc when not memory safe, these are ok to access, e.g. SIMD_Int32x4_load(HEAP8, ...)
                        invalidateCalls(tracked);
                        *callsInvalidated = true
                    }
                },
                UnaryPrefix(_, ref mut right) => {
                    traverseInOrder!(right, false)
                },
                Num(_) | Toplevel(_) | Str(_) | Break(_) | Continue(_) | Dot(_, _) => (), // dot can only be STRING_TABLE.*
                Call(_, _) => {
                    {
                    let (fnexpr, args) = node.getMutCall();
                    // Named functions never change and are therefore safe to not track
                    if !fnexpr.isName() {
                        traverseInOrder!(fnexpr, false)
                    }
                    for arg in args.iter_mut() {
                        traverseInOrder!(arg, false)
                    }
                    }
                    if callHasSideEffects(node) {
                        // these two invalidations will also invalidate calls
                        if !*globalsInvalidated {
                            invalidateGlobals(tracked);
                            *globalsInvalidated = true
                        }
                        if !*memoryInvalidated {
                            invalidateMemory(tracked);
                            *memoryInvalidated = true
                        }
                    }
                },
                If(ref mut cond, ref mut iftrue, ref mut maybeiffalse) => {
                    if *allowTracking {
                        traverseInOrder!(cond, false); // can eliminate into condition, but nowhere else
                        if !*callsInvalidated { // invalidate calls, since we cannot eliminate them into an if that may not execute!
                            invalidateCalls(tracked);
                            *callsInvalidated = true
                        }
                        *allowTracking = false;
                        traverseInOrder!(iftrue, false); // 2 and 3 could be 'parallel', really..
                        if let Some(ref mut iffalse) = *maybeiffalse { traverseInOrder!(iffalse, false) }
                        *allowTracking = true
                    } else {
                        tracked.clear()
                    }
                }
                Block(_) => {
                    // RSTODO: why getstatements here?
                    let maybestats = getStatements(node);
                    if let Some(stats) = maybestats {
                        for stat in stats.iter_mut() {
                            traverseInOrder!(stat, false)
                        }
                    }
                },
                Stat(ref mut stat) => {
                    traverseInOrder!(stat, false)
                },
                Label(_, ref mut body) => {
                    traverseInOrder!(body, false)
                },
                Seq(ref mut left, ref mut right) => {
                    traverseInOrder!(left, false);
                    traverseInOrder!(right, false);
                },
                Do(ref mut cond, ref mut body) => {
                    if let Num(0f64) = **cond { // one-time loop
                        traverseInOrder!(body, false)
                    } else {
                        tracked.clear()
                    }
                },
                Return(ref mut mayberetval) => {
                    if let Some(ref mut retval) = *mayberetval { traverseInOrder!(retval, false) }
                },
                Conditional(ref mut cond, ref mut iftrue, ref mut iffalse) => {
                    if !*callsInvalidated { // invalidate calls, since we cannot eliminate them into a branch of an LLVM select/JS conditional that does not execute
                        invalidateCalls(tracked);
                        *callsInvalidated = true
                    }
                    traverseInOrder!(cond, false);
                    traverseInOrder!(iftrue, false);
                    traverseInOrder!(iffalse, false);
                },
                Switch(ref mut input, ref mut cases) => {
                    traverseInOrder!(input, false);
                    let originalTracked = tracked.keys().cloned().collect::<HashSet<IString>>();
                    for &mut (ref caseordefault, ref mut code) in cases.iter_mut() {
                        if let Some(ref case) = *caseordefault {
                            assert!(if case.isNum() { true } else if let UnaryPrefix(_, mast!(Num(_))) = **case { true } else { false })
                        }
                        for codepart in code.iter_mut() {
                            traverseInOrder!(codepart, false)
                        }
                        // We cannot track from one switch case into another if there are external dependencies, undo all new trackings
                        // Otherwise we can track, e.g. a var used in a case before assignment in another case is UB in asm.js, so no need for the assignment
                        // TODO: general framework here, use in if-else as well
                        let toDelete: Vec<_> = tracked.iter().filter_map(|(k, info)| {
                            if !originalTracked.contains(k) && (info.usesGlobals || info.usesMemory || info.hasDeps) { Some(k.clone()) } else { None }
                        }).collect();
                        for name in toDelete { tracked.remove(&name).unwrap(); }
                    }
                    tracked.clear(); // do not track from inside the switch to outside
                },
                _ => {
                    // RSTODO: note that for is not handled here because fastcomp never generated it so the original optimizer didn't touch it
                    assert!(match *node { New(_) | Object(_) | Defun(_, _, _) | While(_, _) | Array(_) => true, _ => false, }); // we could handle some of these, TODO, but nontrivial (e.g. for while, the condition is hit multiple times after the body)
                    tracked.clear();
                    *abort = true
                },
            }
        }
        traverseInOrder(node, false, memSafe, asmDataLocals, &uses, &potentials, &sideEffectFree, &mut varsToRemove, &varsToTryToRemove, &mut depMap, tracked, &mut globalsInvalidated, &mut memoryInvalidated, &mut callsInvalidated, &mut abort, &mut allowTracking);
    };
    //var eliminationLimit = 0; // used to debugging purposes
    fn doEliminate(name: &IString, node: *mut AstValue, sideEffectFree: &HashSet<IString>, varsToRemove: &mut HashMap<IString, isize>, tracked: &mut HashMap<IString, Tracking>) {
        //if (eliminationLimit == 0) return;
        //eliminationLimit--;
        //printErr('elim!!!!! ' + name);
        // yes, eliminate!
        let name = &name.clone();
        let prev = varsToRemove.insert(name.clone(), 2); // both assign and var definitions can have other vars we must clean up
        assert!(prev.is_none() || prev.unwrap() == 1);
        {
        let info = tracked.get(name).unwrap();
        // RSTODO: tread very very carefully here - node and defnode may be the same. If they *are* the same, we could
        // hit UB with references, node is passed in as a pointer. This is then fine. However, if they are *not* the same
        // then the situation is much less clear - traverseInOrder still holds a &mut to the parent which could allow
        // the compiler to assume that defNode is not changed because the only active mutable reference is to parent,
        // which is used to create the pointer to node. See https://github.com/nikomatsakis/rust-memory-model/issues/1
        // Also be aware that swapping and removal can corrupt references into the nodes. In particular, the name passed
        // in as an argument to this function!
        let defNode = info.defNode;
        if !sideEffectFree.contains(name) {
            // assign
            let value = unsafe { if let Assign(_, _, ref mut val) = *defNode { mem::replace(val, makeEmpty()) } else { panic!() } };
            // wipe out the assign
            unsafe { ptr::replace(defNode, *makeEmpty()) };
            // replace this node in-place
            unsafe { ptr::replace(node, *value) };
        } else {
            // This has no side effects and no uses, empty it out in-place
            unsafe { ptr::replace(node, *makeEmpty()) };
        }
        }
        tracked.remove(name).unwrap();
    }
    // RSTODO: I have a vague feeling this traversePre might be horribly inefficient here - traverseInOrder already descends into
    // things, so why do so in traversePre as well?
    traversePreMut(asmData.func, |block: &mut AstValue| {
        // RSTODO: if we had a macro for concisely expressing profiling, this could be inlined
        macro_rules! doscan {
            ($( $arg:expr ),*) => {{
                #[cfg(feature = "profiling")]
                {
                tstmtelim += start.elapsed().unwrap();
                start = SystemTime::now();
                }
                scan($( $arg ),+);
                #[cfg(feature = "profiling")]
                {
                tstmtscan += start.elapsed().unwrap();
                start = SystemTime::now();
                }
            }};
        }
        // Look for statements, including while-switch pattern
        // RSTODO: lexical borrow issue https://github.com/rust-lang/rust/issues/28449
        let stats = if let Some(stats) = getStatements(unsafe { &mut *(block as *mut _) }) {
            stats
        } else {
            if let While(_, ref mut node @ mast!(Switch(_, _))) = *block {
                // RSNOTE: this is basically the full loop below, hand optimised for a single switch
                doscan!(node, asmDataLocals, &mut tracked)
            }
            return
        };
        tracked.clear();
        let mut returnfound = None;
        for (i, stat) in stats.iter_mut().enumerate() {
            let node = mutDeStat(stat);
            match *node {
                // Check for things that affect elimination
                // do is checked carefully, however
                Assign(..) | Call(..) | If(..) | Toplevel(..) | Do(..) | Return(..) | Label(..) | Switch(..) | Binary(..) | UnaryPrefix(..) => {
                    doscan!(node, asmDataLocals, &mut tracked);
                    if node.isReturn() {
                        returnfound = Some(i);
                        break
                    }
                },
                // asm normalisation has reduced 'var' to just the names
                Var(_) => (),
                // not a var or assign, break all potential elimination so far
                _ => {
                    tracked.clear()
                },
            }
        }
        if let Some(reti) = returnfound {
            // remove any code after a return
            stats.truncate(reti+1)
        }
    });
    }

    #[cfg(feature = "profiling")]
    {
    tstmtelim += start.elapsed().unwrap();
    start = SystemTime::now();
    }

    let mut seenUses = HashMap::<IString, usize>::new();
    let mut helperReplacements = HashMap::<IString, IString>::new(); // for looper-helper optimization

    // clean up vars, and loop variable elimination
    traversePrePostMut(asmData.func, |node: &mut AstValue| {
        // pre
        /*if (type == VAR) {
          node[1] = node[1].filter(function(pair) { return !varsToRemove[pair[0]] });
          if (node[1]->size() == 0) {
            // wipe out an empty |var;|
            node[0] = TOPLEVEL;
            node[1] = [];
          }
        } else */
        // RSTODO: match two things as being the same?
        let elim = if let Assign(true, mast!(Name(ref x)), mast!(Name(ref y))) = *node { x == y } else { false };
        if elim {
            // elimination led to X = X, which we can just remove
            *node = *makeEmpty()
        }
    }, |node: &mut AstValue| {
        // post
        match *node {
            Name(ref mut name) => {
                if let Some(replacement) = helperReplacements.get(name) {
                    *name = replacement.clone();
                    return // no need to track this anymore, we can't loop-optimize more than once
                }
                // track how many uses we saw. we need to know when a variable is no longer used (hence we run this in the post)
                *seenUses.entry(name.clone()).or_insert(0) += 1
            },
            While(_, ref mut body) => {
                // try to remove loop helper variables specifically
                let (stats,) = body.getMutBlock();
                let mut loopers = vec![];
                let mut helpers = vec![];
                let flip;
                let numassigns;
                {
                let last = if let Some(last) = stats.last_mut() { last } else { return };
                // RSTODO: why does last have to be moved?
                let (mut iftruestats, mut iffalsestats) = if let If(_, mast!(Block(ref mut ift)), Some(mast!(Block(ref mut iff)))) = **{last} { (ift, iff) } else { return };
                clearEmptyNodes(iftruestats);
                clearEmptyNodes(iffalsestats);
                if let Some(&mast!(Break(_))) = iffalsestats.last() { // canonicalize break in the if-true
                    // RSNOTE: we're not swapping in the ast, we're preparing for it to happen later
                    mem::swap(&mut iftruestats, &mut iffalsestats);
                    flip = true
                } else if let Some(&mast!(Break(_))) = iftruestats.last() {
                    flip = false
                } else { return }
                let assigns = iffalsestats;
                numassigns = assigns.len();
                // RSTODO: uhhh...we just did this?
                clearEmptyNodes(assigns);
                for stat in assigns.iter() {
                    if let Stat(mast!(Assign(true, Name(ref looper), Name(ref helper)))) = **stat {
                        // RSTODO: all these unwraps valid?
                        if *definitions.get(helper).unwrap_or(&0) == 1 &&
                                *seenUses.get(looper).unwrap() as isize ==
                                *namings.get(looper).unwrap() &&
                                !helperReplacements.contains_key(helper) &&
                                !helperReplacements.contains_key(looper) {
                            loopers.push(looper.clone());
                            helpers.push(helper.clone())
                        }
                    }
                }
                // remove loop vars that are used in the rest of the else
                for stat in assigns.iter() {
                    let assign = if let Stat(mast!(ref assign @ Assign(_, _, _))) = **stat { assign } else { continue };
                    let (&boo, name1, name2) = assign.getAssign();
                    let isloopassign = if boo && name1.isName() && name2.isName() {
                        let (name1,) = name1.getName();
                        loopers.iter().any(|l| l == name1)
                    } else {
                        false
                    };
                    if isloopassign { continue }
                    // this is not one of the loop assigns
                    traversePre(assign, |node: &AstValue| {
                        let name = if let Name(ref name) = *node { name } else { return };
                        let pos = loopers.iter().position(|l| l == name).or_else(|| helpers.iter().position(|h| h == name));
                        if let Some(index) = pos {
                            loopers.remove(index);
                            helpers.remove(index);
                        }
                    })
                }
                // remove loop vars that are used in the if
                for stat in iftruestats.iter() {
                    traversePre(stat, |node: &AstValue| {
                        let name = if let Name(ref name) = *node { name } else { return };
                        let pos = loopers.iter().position(|l| l == name).or_else(|| helpers.iter().position(|h| h == name));
                        if let Some(index) = pos {
                            loopers.remove(index);
                            helpers.remove(index);
                        }
                    })
                }
                }
                if loopers.is_empty() { return }
                for (looper, helper) in loopers.iter().zip(helpers.iter()) {
                    // the remaining issue is whether loopers are used after the assignment to helper and before the last line (where we assign to it)
                    let mut found = None;
                    for (i, stat) in stats[..stats.len()-1].iter().enumerate().rev() {
                        if let Stat(mast!(Assign(true, Name(ref to), _))) = **stat {
                            if to == helper {
                                found = Some(i);
                                break
                            }
                        }
                    }
                    // RSTODO: why return rather than continue?
                    let found = if let Some(found) = found { found } else { return };
                    // if a loop variable is used after we assigned to the helper, we must save its value and use that.
                    // (note that this can happen due to elimination, if we eliminate an expression containing the
                    // loop var far down, past the assignment!)
                    // first, see if the looper and helpers overlap. Note that we check for this looper, compared to
                    // *ALL* the helpers. Helpers will be replaced by loopers as we eliminate them, potentially
                    // causing conflicts, so any helper is a concern.
                    let mut firstLooperUsage = None;
                    let mut lastLooperUsage = None;
                    let mut firstHelperUsage = None;
                    for (i, stat) in stats[found+1..].iter().enumerate() {
                        let i = i + found+1;
                        let curr = if i < stats.len()-1 { stat } else { let (cond, _, _) = stat.getIf(); cond }; // on the last line, just look in the condition
                        traversePre(curr, |node: &AstValue| {
                            if let Name(ref name) = *node {
                                if name == looper {
                                    firstLooperUsage = firstLooperUsage.or_else(|| Some(i));
                                    lastLooperUsage = Some(i);
                                } else if helpers.iter().any(|h| h == name) {
                                    firstHelperUsage = firstHelperUsage.or_else(|| Some(i));
                                }
                            }
                        })
                    }
                    if let Some(firstLooperUsage) = firstLooperUsage {
                        let lastLooperUsage = lastLooperUsage.unwrap();
                        // the looper is used, we cannot simply merge the two variables
                        if (firstHelperUsage.is_none() || firstHelperUsage.unwrap() > lastLooperUsage) && lastLooperUsage+1 < stats.len() && triviallySafeToMove(&stats[found], asmDataLocals) && *seenUses.get(helper).unwrap() as isize == *namings.get(helper).unwrap() {
                            // the helper is not used, or it is used after the last use of the looper, so they do not overlap,
                            // and the last looper usage is not on the last line (where we could not append after it), and the
                            // helper is not used outside of the loop.
                            // just move the looper definition to after the looper's last use
                            // RSTODO: doing it in two steps means some elements will get shifted twice, ideally would be one op
                            let node = stats.remove(found);
                            // RSNOTE: inserts after the lastLooperUsage, because everything has moved left
                            stats.insert(lastLooperUsage, node);
                        } else {
                            // they overlap, we can still proceed with the loop optimization, but we must introduce a
                            // loop temp helper variable
                            let temp = IString::from(format!("{}$looptemp", looper));
                            assert!(!asmDataLocals.contains_key(&temp));
                            let statslen = stats.len();
                            for (i, stat) in stats[firstLooperUsage..lastLooperUsage+1].iter_mut().enumerate() {
                                let i = i + firstLooperUsage;
                                let curr = if i < statslen-1 { stat } else { let (cond, _, _) = stat.getMutIf(); cond }; // on the last line, just look in the condition

                                fn looperToLooptemp(node: &mut AstValue, looper: &IString, temp: &IString) -> bool {
                                    match *node {
                                        Name(ref mut name) => {
                                            if name == looper {
                                                *name = temp.clone()
                                            }
                                        },
                                        Assign(_, mast!(Name(_)), ref mut right) => {
                                            // do not traverse the assignment target, phi assignments to the loop variable must remain
                                            traversePrePostConditionalMut(right, |node: &mut AstValue| looperToLooptemp(node, looper, temp), |_| ());
                                            return false
                                        },
                                        _ => (),
                                    };
                                    true
                                }
                                traversePrePostConditionalMut(curr, |node: &mut AstValue| looperToLooptemp(node, looper, &temp), |_| ());
                            }
                            let tempty = AsmData::getTypeFromLocals(asmDataLocals, looper).unwrap();
                            AsmData::addVarToLocalsAndVars(asmDataLocals, asmDataVars, temp.clone(), tempty);
                            stats.insert(found, an!(Stat(an!(Assign(true, makeName(temp), makeName(looper.clone()))))));
                        }
                    }
                }
                for (i, h1) in helpers.iter().enumerate() {
                    for h2 in helpers[i+1..].iter() {
                        if h1 == h2 { return } // it is complicated to handle a shared helper, abort
                    }
                }
                // hurrah! this is safe to do
                for (looper, helper) in loopers.iter().zip(helpers.iter()) {
                    let prev = varsToRemove.insert(helper.clone(), 2);
                    assert!(prev.is_none());
                    for stat in stats.iter_mut() {
                        traversePreMut(stat, |node: &mut AstValue| { // replace all appearances of helper with looper
                            if let Name(ref mut name) = *node {
                                if name == helper { *name = looper.clone() }
                            }
                        });
                    }
                    let prev = helperReplacements.insert(helper.clone(), looper.clone()); // replace all future appearances of helper with looper
                    assert!(prev.is_none());
                    let prev = helperReplacements.insert(looper.clone(), looper.clone()); // avoid any further attempts to optimize looper in this manner (seenUses is wrong anyhow, too)
                    assert!(prev.is_none());
                }
                // simplify the if. we remove the if branch, leaving only the else
                let last = stats.last_mut().unwrap();
                let (cond, iftrue, maybeiffalse) = last.getMutIf();
                if flip {
                    let oldcond = mem::replace(cond, makeEmpty());
                    *cond = an!(UnaryPrefix(is!("!"), oldcond));
                    simplifyNotCompsDirect(cond, &mut asmFloatZero);
                    mem::swap(iftrue, maybeiffalse.as_mut().unwrap());
                }
                if loopers.len() == numassigns {
                    *maybeiffalse = None;
                } else {
                    let iffalse = maybeiffalse.as_mut().unwrap();
                    for stat in getStatements(iffalse).unwrap().iter_mut() {
                        let shouldempty = if let Assign(_, mast!(Name(ref name)), _) = *deStat(stat) {
                            loopers.iter().any(|l| l == name)
                        } else {
                            false
                        };
                        if shouldempty { *stat = makeEmpty() }
                    }
                }
            },
            _ => (),
        }
    });

    #[cfg(feature = "profiling")]
    {
    tcleanvars += start.elapsed().unwrap();
    start = SystemTime::now();
    }
    }

    for (name, &val) in varsToRemove.iter() {
        if val == 2 && asmData.isVar(name) { asmData.deleteVar(name) }
    }

    asmData.denormalize();

    #[cfg(feature = "profiling")]
    {
    treconstruct += start.elapsed().unwrap();
    //start = SystemTime::now();
    }

    });

    removeAllEmptySubNodes(ast);

    #[cfg(feature = "profiling")]
    {
    printlnerr!("    EL stages: a:{} fe:{} vc:{} se:{} (ss:{}) cv:{} r:{}",
      tasmdata.to_us(), tfnexamine.to_us(), tvarcheck.to_us(), tstmtelim.to_us(), tstmtscan.to_us(), tcleanvars.to_us(), treconstruct.to_us());
    }
}

pub fn simplifyExpressions(ast: &mut AstValue, preciseF32: bool) {
    // Simplify common expressions used to perform integer conversion operations
    // in cases where no conversion is needed.
    fn simplifyIntegerConversions(ast: &mut AstValue) {
        traversePreMut(ast, |node: &mut AstValue| {
            match *node {
                Binary(is!(">>"), mast!(Binary(is!("<<"), Binary(is!("&"), _, Num(mask)), Num(s1))), mast!(Num(s2))) if s1 == s2 => {
                    let shifts = s1;
                    if !(isInteger32(mask) && isInteger32(shifts) && ((jsD2I(mask) << jsD2I(shifts)) >> jsD2I(shifts)) == jsD2I(mask)) { return }
                    // Transform (x&A)<<B>>B to X&A
                    // RSTODO: lexical borrows strike again - we should be able to bind innernode in the match itself
                    let innerNode = {
                        let (_, inner1, _) = node.getMutBinary();
                        let (_, inner2, _) = inner1.getMutBinary();
                        mem::replace(inner2, makeEmpty())
                    };
                    *node = *innerNode;
                },
                Binary(ref op, ref mut node1, ref mut node2) if BITWISE.contains(op) => {
                    fn simplify(subNode: &mut AstValue) {
                        if let Binary(is!("&"), mast!(Binary(_, _, _)), mast!(Num(1f64))) = *subNode {
                            // Rewrite (X < Y) & 1 to X < Y , when it is going into a bitwise operator. We could
                            // remove even more (just replace &1 with |0, then subsequent passes could remove the |0)
                            // but v8 issue #2513 means the code would then run very slowly in chrome.
                            // RSTODO: more lexical borrow issue
                            let input = {
                                let (_, input, _) = subNode.getMutBinary();
                                {
                                let (op, _, _) = input.getBinary();
                                if !COMPARE_OPS.contains(op) { return }
                                }
                                mem::replace(input, makeEmpty())
                            };
                            *subNode = *input;
                        }
                    }
                    simplify(node1);
                    simplify(node2);
                },
                _ => (),
            }
        })
    }

    // When there is a bunch of math like (((8+5)|0)+12)|0, only the external |0 is needed, one correction is enough.
    // At each node, ((X|0)+Y)|0 can be transformed into (X+Y): The inner corrections are not needed
    // TODO: Is the same is true for 0xff, 0xffff?
    // Likewise, if we have |0 inside a block that will be >>'d, then the |0 is unnecessary because some
    // 'useful' mathops already |0 anyhow.

    fn simplifyOps(ast: &mut AstValue, asmFloatZero: &mut Option<IString>, preciseF32: bool) {
        fn removeMultipleOrZero(ast: &mut AstValue) {
            let mut rerun = true;
            while rerun {
                rerun = false;
                let stack = UnsafeCell::new(vec![]);
                let process = |node: &mut AstValue| {
                    processInner(node, &mut rerun, unsafe { &mut *stack.get() })
                };
                fn processInner(node: &mut AstValue, rerun: &mut bool, stack: &mut Vec<isize>) {
                    // RSTODO: the only reason the node unsafecell stuff is here is because of lexical
                    // lifetimes not understanding that we can assign to node at the end of match arms
                    match *node {
                        Binary(is!("|"), mast!(Num(nleft)), mast!(Num(nright))) => {
                            stack.push(0);
                            *node = Num((jsD2I(nleft) | jsD2I(nright)) as f64)
                        },
                        Binary(is!("|"), _, _) => {
                            {
                            let (_, left, right) = node.getMutBinary();
                            let go = if let Num(0f64) = **left {
                                // canonicalize order
                                mem::swap(left, right);
                                true
                            } else if let Num(0f64) = **right {
                                true
                            } else {
                                false
                            };
                            if !go {
                                stack.push(1);
                                return
                            }
                            }
                            // We might be able to remove this correction
                            for i in (0..stack.len()).rev() {
                                let stackval = stack[i];
                                if stackval >= 1 {
                                    let newnode;
                                    {
                                    let (_, left, right) = node.getMutBinary();
                                    let stackbackval = *stack.last().unwrap();
                                    if stackbackval < 2 && left.isCall() { break } // we can only remove multiple |0s on these
                                    if stackbackval < 1 && match **left { Sub(_, _) | UnaryPrefix(_, _) => /* ops that in asm must be coerced right away */ true, Binary(ref op, _, _) if COERCION_REQUIRING_BINARIES.contains(op) => true, _ => false } { break } // we can remove |0 or >>2
                                    // we will replace ourselves with the non-zero side. Recursively process that node.
                                    newnode = mem::replace(if let Num(0f64) = **left { right } else { left }, makeEmpty())
                                    }
                                    *node = *newnode;
                                    *rerun = true;
                                    processInner(node, rerun, stack);
                                    return
                                } else if stackval == -1 {
                                    break // Too bad, we can't
                                }
                            }
                            stack.push(2) // From here on up, no need for this kind of correction, it's done at the top
                                          // (Add this at the end, so it is only added if we did not remove it)
                        },
                        Binary(ref op, _, _) if USEFUL_BINARY_OPS.contains(op) => {
                            stack.push(1)
                        },
                        // RSTODO: should be connected to num and name, see https://github.com/rust-lang/rfcs/pull/99
                        Binary(ref op, _, _) if SAFE_BINARY_OPS.contains(op) => {
                            stack.push(0) // This node is safe in that it does not interfere with this optimization
                        },
                        Num(_) |
                        Name(_) => {
                            stack.push(0) // This node is safe in that it does not interfere with this optimization
                        },
                        UnaryPrefix(is!("~"), _) => {
                            stack.push(1)
                        },
                        _ => {
                            stack.push(-1) // This node is dangerous! Give up if you see this before you see '1'
                        },
                    }
                };

                traversePrePostMut(ast, process, |_| {
                    let stack = unsafe { &mut *stack.get() };
                    assert!(!stack.is_empty());
                    stack.pop().unwrap();
                })
            }
        }

        removeMultipleOrZero(ast);

        // & and heap-related optimizations

        let mut hasTempDoublePtr = false;
        let mut rerunOrZeroPass = false;

        traversePrePostConditionalMut(ast, |node: &mut AstValue| {
            // Detect trees which should not
            // be simplified.
            match *node {
                // do not traverse subchildren here, we should not collapse 55 & 126.
                Sub(mast!(Name(ref name)), _) if isFunctionTable(name) => false,
                _ => true,
            }
        }, |node: &mut AstValue| {
            // Simplifications are done now so
            // that we simplify a node's operands before the node itself. This allows
            // optimizations to cascade.
            match *node {
                Name(is!("tempDoublePtr")) => hasTempDoublePtr = true,
                Binary(is!("&"), mast!(Num(n1)), mast!(Num(n2))) => {
                    *node = *makeNum((jsD2I(n1) & jsD2I(n2)) as f64)
                },
                Binary(is!("&"), ref mut input @ mast!(Binary(is!("&"), _, Num(_))), mast!(Num(ref mut amount))) => {
                    // Collapse X & 255 & 1
                    let newinput = {
                        let (_, inputleft, inputright) = input.getMutBinary();
                        let (&inputamount,) = inputright.getNum();
                        *amount = (jsD2I(*amount) & jsD2I(inputamount)) as f64;
                        mem::replace(inputleft, makeEmpty())
                    };
                    *input = newinput
                },
                Binary(ref mut op @ is!("&"), mast!(Sub(Name(ref mut name), _)), mast!(Num(ref mut amount))) => {
                    // HEAP8[..] & 255 => HEAPU8[..]
                    if let Some(hi) = parseHeap(name) {
                        if isInteger32(*amount) && *amount == f64::powf(2.0, hi.bits as f64) - 1f64 {
                            if !hi.unsign {
                                *name = getHeapStr(hi.bits, true) // make unsigned
                            }
                            // we cannot return HEAPU8 without a coercion, but at least we do HEAP8 & 255 => HEAPU8 | 0
                            *op = is!("|");
                            *amount = 0f64
                        }
                    }
                },
                Binary(is!("&"), mast!(Binary(is!(">>"), Binary(is!("<<"), _, Num(n1)), Num(n2))), mast!(Num(amount)))
                        if f64toi32(n1) == f64toi32(n2) && (!(0xFFFFFFFFu32 as i32 >> f64toi32(n2))) & jsD2I(amount) == 0 => {
                    // x << 24 >> 24 & 255 => x & 255
                    // RSTODO: lexical lifetime inconvenience
                    let (_, input, _) = node.getMutBinary();
                    let newinput = {
                        let (_, inputinner, _) = input.getMutBinary();
                        let (_, newinput, _) = inputinner.getMutBinary();
                        mem::replace(newinput, makeEmpty())
                    };
                    *input = newinput
                },
                Binary(is!("^"), _, mast!(UnaryPrefix(is!("-"), Num(1f64)))) => {
                    // RSTODO: more lexical lifetime problems
                    // LLVM represents bitwise not as xor with -1. Translate it back to an actual bitwise not.
                    let maybeval = {
                        let (_, val, _) = node.getMutBinary();
                        // avoid creating ~~~ which is confusing for asm given the role of ~~
                        if let UnaryPrefix(is!("~"), _) = **val { None } else { Some(mem::replace(val, makeEmpty())) }
                    };
                    if let Some(val) = maybeval {
                        *node = UnaryPrefix(is!("~"), val)
                    }
                },
                Binary(ref mut op @ is!(">>"), ref mut inner @ mast!(Binary(is!("<<"), Sub(Name(_), _), Num(_))), mast!(Num(ref mut amount))) => {
                    // collapse HEAPU?8[..] << 24 >> 24 etc. into HEAP8[..] | 0
                    // RSTODO: lexical lifetimes
                    let newinner = {
                        let mut replaceinner = false;
                        let (_, innersub, innernum) = inner.getMutBinary();
                        let (&mut inneramount,) = innernum.getMutNum();
                        if *amount == inneramount {
                            let (subleft, _) = innersub.getMutSub();
                            let (subname,) = subleft.getMutName();
                            if let Some(hi) = parseHeap(subname) {
                                if hi.bits == 32 - f64tou32(*amount) {
                                    *subname = getHeapStr(hi.bits, false);
                                    *op = is!("|");
                                    replaceinner = true;
                                    *amount = 0f64;
                                    rerunOrZeroPass = true
                                }
                            }
                        }
                        if replaceinner { Some(mem::replace(innersub, makeEmpty())) } else { None }
                    };
                    if let Some(newinner) = newinner {
                        *inner = newinner
                    }
                },
                Assign(b, ref mut target, ref mut value) => {
                    // optimizations for assigning into HEAP32 specifically
                    assert!(b);
                    if let Sub(mast!(Name(ref name)), _) = **target {
                        match *name {
                            is!("HEAP32") => {
                                // HEAP32[..] = x | 0 does not need the | 0 (unless it is a mandatory |0 of a call)
                                let maybenewvalue = match **value {
                                    Binary(is!("|"), mast!(Num(0f64)), ref mut newvalue) |
                                    Binary(is!("|"), ref mut newvalue, mast!(Num(0f64))) if
                                        !newvalue.isCall() => {
                                        Some(mem::replace(newvalue, makeEmpty()))
                                    },
                                    _ => None,
                                };
                                if let Some(newvalue) = maybenewvalue {
                                    *value = newvalue
                                }
                            },
                            is!("HEAP8") => {
                                // HEAP8[..] = x & 0xff does not need the & 0xff
                                // RSTODO: lexical lifetimes
                                if let Binary(is!("&"), _, mast!(Num(255f64))) = **value {
                                    let newvalue = {
                                        let (_, newvalue, _) = value.getMutBinary();
                                        mem::replace(newvalue, makeEmpty())
                                    };
                                    *value = newvalue
                                }
                            },
                            is!("HEAP16") => {
                                // HEAP16[..] = x & 0xffff does not need the & 0xffff
                                // RSTODO: lexical lifetimes
                                if let Binary(is!("&"), _, mast!(Num(65535f64))) = **value {
                                    let newvalue = {
                                        let (_, newvalue, _) = value.getMutBinary();
                                        mem::replace(newvalue, makeEmpty())
                                    };
                                    *value = newvalue
                                }
                            },
                            _ => (),
                        }
                    }
                    // RSTODO: https://github.com/rust-lang/rust/issues/30104
                    use std::ops::DerefMut;
                    let mut maybenewvalue = None;
                    if let Binary(is!("|"), ref mut left, ref mut right) = *value.deref_mut() {
                        // canonicalize order of |0 to end
                        if let Num(0f64) = **left {
                            mem::swap(left, right)
                        }
                        // if a seq ends in an |0, remove an external |0
                        // note that it is only safe to do this in assigns, like we are doing here (return (x, y|0); is not valid)
                        let shouldswap = if let Seq(_, mast!(Binary(ref op, _, _))) = **left { USEFUL_BINARY_OPS.contains(op) } else { false };
                        if shouldswap {
                            maybenewvalue = Some(mem::replace(left, makeEmpty()))
                        }
                    }
                    if let Some(newvalue) = maybenewvalue {
                        *value = newvalue;
                    }
                },
                Binary(is!(">>"), mast!(Num(n1)), mast!(Num(n2))) => {
                    // optimize num >> num, in asm we need this since we do not optimize shifts in asm.js
                    *node = Num((jsD2I(n1) >> jsD2I(n2)) as f64)
                },
                Binary(is!("+"), mast!(Num(n1)), mast!(Num(n2))) => {
                    // The most common mathop is addition, e.g. in getelementptr done repeatedly. We can join all of those,
                    // by doing (num+num) ==> newnum.
                    *node = Num((jsD2I(n1) + jsD2I(n2)) as f64)
                },
                _ => (),
            }
        });

        if rerunOrZeroPass { removeMultipleOrZero(ast) }

        if !hasTempDoublePtr { return }
        let mut asmData = AsmData::new(ast);
        {
        let asmDataLocals = &asmData.locals;
        traversePreMut(asmData.func, |node: &mut AstValue| {
            match *node {
                Assign(b, mast!(Sub(Name(ref mut heapname @ is!("HEAP32")), _)), ref mut value) => {
                    assert!(b);
                    // remove bitcasts that are now obviously pointless, e.g.
                    // HEAP32[$45 >> 2] = HEAPF32[tempDoublePtr >> 2] = ($14 < $28 ? $14 : $28) - $42, HEAP32[tempDoublePtr >> 2] | 0;
                    // RSTODO: lexical lifetimes
                    let mut maybenewvalue = None;
                    if let Seq(mast!(Assign(_, Sub(Name(is!("HEAPF32")), Binary(_, Name(is!("tempDoublePtr")), _)), ref mut newvalue)), _) = **value {
                        // transform to HEAPF32[$45 >> 2] = ($14 < $28 ? $14 : $28) - $42;
                        *heapname = is!("HEAPF32");
                        maybenewvalue = Some(mem::replace(newvalue, makeEmpty()))
                    }
                    if let Some(newvalue) = maybenewvalue {
                        *value = newvalue
                    }
                },
                Seq(_, _) => {
                    // (HEAP32[tempDoublePtr >> 2] = HEAP32[$37 >> 2], +HEAPF32[tempDoublePtr >> 2])
                    //   ==>
                    // +HEAPF32[$37 >> 2]
                    // RSTODO: lexical lifetimes...maybe
                    use std::ops::DerefMut;
                    let maybenewpart;
                    {
                    // RSTODO: https://github.com/rust-lang/rust/issues/30104
                    let mut node = &mut *node;
                    maybenewpart = match *node.deref_mut() {
                        Seq(mast!(Assign(b, Sub(Name(ref mut n1), Binary(_, Name(is!("tempDoublePtr")), _)), ref mut newpart @ Sub(Name(_), _))), ref mut nextseq) if
                                (*n1 == is!("HEAP32") || *n1 == is!("HEAPF32")) &&
                                !nextseq.isSeq() => { // avoid (x, y, z) which can be used for tempDoublePtr on doubles for alignment fixes
                            // RSTODO: lexical lifetimes strike again - this condition should be part of the match above (so we'd never return
                            // None from this match arm, but you can't have submatches of an @ match
                            let n2 = {
                                let (left, _) = newpart.getSub();
                                let (name,) = left.getName();
                                name.clone()
                            };
                            if n2 == is!("HEAP32") || n2 == is!("HEAPF32") {
                                assert!(b);
                                // RSTODO: valid assertion?
                                assert!(*n1 == n2);
                                Some((n1.clone(), mem::replace(newpart, makeEmpty())))
                            } else {
                                None
                            }
                        },
                        _ => None,
                    };
                    }
                    match maybenewpart {
                        Some((is!("HEAP32"), mut newpart)) => {
                            {
                                let (left, _) = newpart.getMutSub();
                                let (name,) = left.getMutName();
                                *name = is!("HEAPF32")
                            }
                            let asmType = {
                                let (_, right) = node.getSeq();
                                detectType(right, Some(asmDataLocals), asmFloatZero, false).unwrap()
                            };
                            *node = *makeAsmCoercion(newpart, asmType)

                        },
                        Some((is!("HEAPF32"), mut newpart)) => {
                            {
                                let (left, _) = newpart.getMutSub();
                                let (name,) = left.getMutName();
                                *name = is!("HEAP32")
                            }
                            *node = *an!(Binary(is!("|"), newpart, makeNum(0f64)))
                        },
                        Some(_) => panic!(),
                        None => (),
                    }
                },
                _ => (),
            }
        });
        }

        // finally, wipe out remaining ones by finding cases where all assignments to X are bitcasts, and all uses are writes to
        // the other heap type, then eliminate the bitcast
        struct BitcastData {
            // RSTODO: could any of the usizes be bools?
            define_HEAP32: usize,
            define_HEAPF32: usize,
            use_HEAP32: usize,
            use_HEAPF32: usize,
            namings: usize,
            defines: Vec<*mut AstValue>,
            uses: Vec<*mut AstValue>,
        }
        let mut bitcastVars = HashMap::<IString, BitcastData>::new();
        traversePreMut(asmData.func, |node: &mut AstValue| {
            let nodeptr = node as *mut _;
            match *node {
                Assign(b1, mast!(Name(ref name)), mast!(Seq(Assign(b2, Sub(Name(ref heap), Binary(_, Name(is!("tempDoublePtr")), _)), _), _))) if
                        *heap == is!("HEAP32") || *heap == is!("HEAPF32") => {
                    assert!(b1 && b2);
                    let entry = bitcastVars.entry(name.clone()).or_insert(BitcastData {
                        define_HEAP32: 0,
                        define_HEAPF32: 0,
                        use_HEAP32: 0,
                        use_HEAPF32: 0,
                        namings: 0,
                        defines: vec![],
                        uses: vec![],
                    });
                    if *heap == is!("HEAP32") {
                        entry.define_HEAP32 += 1
                    } else {
                        assert!(*heap == is!("HEAPF32"));
                        entry.define_HEAPF32 += 1
                    }
                    entry.defines.push(nodeptr)
                },
                _ => (),
            }
        });
        traversePreMut(asmData.func, |node: &mut AstValue| {
            let nodeptr = node as *mut _;
            match *node {
                Name(ref name) => {
                    if let Some(val) = bitcastVars.get_mut(name) { val.namings += 1 }
                },
                Assign(b, mast!(Sub(Name(ref heap), _)), mast!(Name(ref name))) if
                        *heap == is!("HEAP32") || *heap == is!("HEAPF32") => {
                    assert!(b);
                    if let Some(val) = bitcastVars.get_mut(name) {
                        match *heap {
                            is!("HEAP32") => val.use_HEAP32 += 1,
                            is!("HEAPF32") => val.use_HEAPF32 += 1,
                            _ => panic!(),
                        }
                        val.uses.push(nodeptr)
                    }
                },
                _ => (),
            }
        });
        for (v, info) in bitcastVars.into_iter() {
            // good variables define only one type, use only one type, have definitions and uses, and define as a different type than they use
            let goodvar = info.define_HEAP32*info.define_HEAPF32 == 0 && info.use_HEAP32*info.use_HEAPF32 == 0 &&
                          info.define_HEAP32+info.define_HEAPF32 > 0  && info.use_HEAP32+info.use_HEAPF32 > 0 &&
                          info.define_HEAP32*info.use_HEAP32 == 0 && info.define_HEAPF32*info.use_HEAPF32 == 0 &&
                          asmData.isLocal(&v) && info.namings == info.define_HEAP32+info.define_HEAPF32+info.use_HEAP32+info.use_HEAPF32;
            if !goodvar { continue }
            let correct = if info.use_HEAP32 > 0 { is!("HEAPF32") } else { is!("HEAP32") };
            for define in info.defines.into_iter() {
                // RSTODO: this could theoretically be UB - the compiler could conclude that nothing has access to asmData and do some
                // optimisation where it figures it can do the denormalize below early, or something equally strange. Search rust
                // memory model and see also doEliminate where there are similar issues
                let define = unsafe { &mut *define };
                let (_, _, defineval) = define.getMutAssign();
                let definepart = {
                    let (left, _) = defineval.getMutSeq();
                    let (_, _, definepart) = left.getMutAssign();
                    mem::replace(definepart, makeEmpty())
                };
                let newdefineval = match correct {
                    is!("HEAP32") => an!(Binary(is!("|"), definepart, makeNum(0f64))),
                    is!("HEAPF32") => makeAsmCoercion(definepart, if preciseF32 { AsmType::Float } else { AsmType::Double }),
                    _ => panic!(),
                };
                *defineval = newdefineval
                // do we want a simplifybitops on the new values here?
            }
            for use_ in info.uses.into_iter() {
                // RSTODO: also potentially UB, see above
                let use_ = unsafe { &mut *use_ };
                let (_, left, _) = use_.getMutAssign();
                let (left, _) = left.getMutSub();
                let (name,) = left.getMutName();
                *name = correct.clone()
            }
            let correctType = match asmData.getType(&v).unwrap() {
                AsmType::Int => if preciseF32 { AsmType::Float } else { AsmType::Double },
                AsmType::Float |
                AsmType::Double => AsmType::Int,
                _ => panic!(),
            };
            asmData.setType(v, correctType)
        }
        asmData.denormalize()
    }

    fn emitsBoolean(node: &AstValue) -> bool {
        match *node {
            Num(n) => n == 0f64 || n == 1f64,
            Binary(ref op, _, _) => COMPARE_OPS.contains(op),
            UnaryPrefix(ref op, _) => *op == is!("!"),
            Conditional(_, ref iftrue, ref iffalse) => emitsBoolean(iftrue) && emitsBoolean(iffalse),
            _ => false,
        }
    }

    //   expensive | expensive can be turned into expensive ? 1 : expensive, and
    //   expensive | cheap     can be turned into cheap     ? 1 : expensive,
    // so that we can avoid the expensive computation, if it has no side effects.
    fn conditionalize(ast: &mut AstValue, asmFloatZero: &mut Option<IString>) {
        traversePreMut(ast, |node: &mut AstValue| {
            {
            const MIN_COST: isize = 7;
            let (_, left, right) = match *node {
                Binary(ref op, ref mut left, ref mut right)
                    if (*op == is!("|") || *op == is!("&")) && !left.isNum() && !right.isNum() => (op, left, right),
                _ => return,
            };
            // logical operator on two non-numerical values
            if !emitsBoolean(left) || !emitsBoolean(right) { return }
            let leftEffects = hasSideEffects(left);
            let rightEffects = hasSideEffects(right);
            if leftEffects && rightEffects { return }
            // canonicalize with side effects, if any, happening on the left
            if rightEffects {
              if measureCost(left) < MIN_COST { return } // avoidable code is too cheap
              mem::swap(left, right)
            } else if leftEffects {
              if measureCost(right) < MIN_COST { return } // avoidable code is too cheap
            } else {
              // no side effects, reorder based on cost estimation
              let leftCost = measureCost(left);
              let rightCost = measureCost(right);
              if cmp::max(leftCost, rightCost) < MIN_COST { return } // avoidable code is too cheap
              if leftCost > rightCost {
                  mem::swap(left, right)
              }
            }
            // worth it, perform conditionalization
            }
            let (op, left, right) = mem::replace(node, *makeEmpty()).intoBinary();
            let mut ret = if op == is!("|") {
                an!(Conditional(left, makeNum(1f64), right))
            } else { // &
                an!(Conditional(left, right, makeNum(0f64)))
            };
            // RSTODO: https://github.com/rust-lang/rust/issues/30104
            use std::ops::DerefMut;
            if let Conditional(ref mut cond @ mast!(UnaryPrefix(is!("!"), _)), ref mut iftrue, ref mut iffalse) = *ret.deref_mut() {
                flipCondition(cond, asmFloatZero);
                mem::swap(iftrue, iffalse)
            }
            *node = *ret
        })
    }

    fn simplifyNotZero(ast: &mut AstValue) {
        traversePreMut(ast, |node: &mut AstValue| {
            match *node {
                If(ref mut boolean, _, _) |
                Do(ref mut boolean, _) |
                While(ref mut boolean, _) |
                Conditional(ref mut boolean, _, _) => {
                    if let Binary(is!("!="), _, mast!(Num(0f64))) = **boolean {
                        let newboolean = {
                            let (_, newboolean, _) = boolean.getMutBinary();
                            mem::replace(newboolean, makeEmpty())
                        };
                        *boolean = newboolean
                    }
                },
                _ => return,
            }
        })
    }

    let mut asmFloatZero = None;

    traverseFunctionsMut(ast, |func: &mut AstValue| {

    simplifyIntegerConversions(func);
    simplifyOps(func, &mut asmFloatZero, preciseF32);
    traversePreMut(func, |node: &mut AstValue| {
        simplifyNotCompsDirect(node, &mut asmFloatZero)
    });
    conditionalize(func, &mut asmFloatZero);
    simplifyNotZero(func);

    })
}

pub fn simplifyIfs(ast: &mut AstValue) {

    let mut asmFloatZero = None;

    traverseFunctionsMut(ast, |func: &mut AstValue| {

    let mut simplifiedAnElse = false;

    traversePreMut(func, |node: &mut AstValue| {
        // simplify   if (x) { if (y) { .. } }   to   if (x ? y : 0) { .. }
        let (cond, iftrue, maybeiffalse) = if let If(ref mut c, ref mut it, ref mut mif) = *node { (c, it, mif) } else { return };
        let mut body = iftrue;
        // recurse to handle chains
        // RSTODO: what if the iftrue is not a block, just a single if?
        while let Block(..) = **body {
            {
            let shouldflip = {
                let (b1stats,) = body.getMutBlock();
                let other = if let Some(o) = b1stats.last() { o } else { break };
                if !other.isIf() {
                    // our if block does not end with an if. perhaps if have an else we can flip
                    // RSTODO: again, what if the iffalse is not a block, just a single if?
                    if let Some(mast!(Block(ref b2stats))) = *maybeiffalse {
                        if let Some(&mast!(If(..))) = b2stats.last() { true } else { break }
                    } else { break }
                } else { false }
            };
            if shouldflip {
                // flip node
                flipCondition(cond, &mut asmFloatZero);
                mem::swap(body, maybeiffalse.as_mut().unwrap())
            }
            }
            let other = {
            let (stats,) = body.getMutBlock();
            // we can handle elses, but must be fully identical
            {
                let other = if let Some(o) = stats.last_mut() { o } else { break };
                let (ocond, oiftrue, omaybeiffalse) = other.getMutIf();
                if maybeiffalse.is_some() || omaybeiffalse.is_some() {
                    let iffalse = if let Some(ref iff) = *maybeiffalse { iff } else { break };
                    if Some(iffalse) != omaybeiffalse.as_ref() {
                        // the elses are different, but perhaps if we flipped a condition we can do better
                        if iffalse == oiftrue {
                            //let oiffalse = omaybeiffalse.as_mut().unwrap();
                            if omaybeiffalse.is_none() { *omaybeiffalse = Some(makeBlock()) }
                            // flip other. note that other may not have had an else! add one if so; we will eliminate such things later
                            flipCondition(ocond, &mut asmFloatZero);
                            mem::swap(oiftrue, omaybeiffalse.as_mut().unwrap())
                        } else { break }
                    }
                }
            }
            if stats.len() > 1 {
                // try to commaify - turn everything between the ifs into a comma operator inside the second if
                let commable = stats[..stats.len()-1].iter().all(|s| commable(deStat(s)));
                // RSTODO: if we break here we've moved around a bunch of stuff,
                // does it matter? Maybe we should check commable earlier?
                if !commable { break }
                let mut other = stats.pop().unwrap();
                {
                let (ocond, _, _) = other.getMutIf();
                let mut tmpcond = makeEmpty();
                mem::swap(&mut tmpcond, ocond);
                for stat in stats.drain(..).rev() {
                    tmpcond = an!(Seq(intoDeStat(stat), tmpcond));
                }
                mem::swap(&mut tmpcond, ocond);
                // RSTODO: resize stats to be smaller?
                }
                stats.push(other)
            }
            // RSTODO: shouldn't this be an abort?
            if stats.len() != 1 { break }
            if maybeiffalse.is_some() { simplifiedAnElse = true }
            stats.pop().unwrap()
            };
            let (ocond, oiftrue, _) = other.intoIf();
            let mut tmpcond = makeEmpty();
            mem::swap(&mut tmpcond, cond);
            tmpcond = an!(Conditional(tmpcond, ocond, an!(Num(0f64))));
            mem::swap(&mut tmpcond, cond);
            *body = oiftrue;
        }
    });

    if simplifiedAnElse {
        // there may be fusing opportunities

        // we can only fuse if we remove all uses of the label. if there are
        // other ones - if the label check can be reached from elsewhere -
        // we must leave it
        let mut abort = false;

        let mut labelAssigns = HashMap::new();

        traversePreMut(func, |node: &mut AstValue| {
            if let Assign(_, mast!(Name(is!("label"))), ref right) = *node {
                if let Num(fvalue) = **right {
                    let value = f64toi32(fvalue);
                    *labelAssigns.entry(value).or_insert(0) += 1
                } else {
                   // label is assigned a dynamic value (like from indirectbr), we cannot do anything
                   abort = true;
                }
            }
        });
        if abort { return }

        let mut labelChecks = HashMap::new();

        traversePreMut(func, |node: &mut AstValue| {
            if let Binary(is!("=="), mast!(Binary(is!("|"), Name(is!("label")), _)), ref right) = *node {
                if let Num(fvalue) = **right {
                    let value = f64toi32(fvalue);
                    *labelChecks.entry(value).or_insert(0) += 1
                } else {
                    // label is checked vs a dynamic value (like from indirectbr), we cannot do anything
                    abort = true;
                }
            }
        });
        if abort { return }

        let inLoop = Cell::new(0); // when in a loop, we do not emit   label = 0;   in the relooper as there is no need
        traversePrePostMut(func, |node: &mut AstValue| {
            if let While(..) = *node { inLoop.set(inLoop.get() + 1) }
            let stats = if let Some(s) = getStatements(node) { s } else { return };
            if stats.is_empty() { return }
            cfor!{let mut i = 0; i < stats.len()-1; i += 1; {
                {
                let (pre, post) = match &mut stats[i..i+2] { &mut [ref mut pre, ref mut post] => (pre, post), _ => panic!() };
                if !pre.isIf() || !post.isIf() { continue }
                let (_, _, premaybeiffalse) = pre.getMutIf();
                let preiffalse = if let Some(ref mut p) = *premaybeiffalse { p } else { continue };
                let (postcond, postiftrue, postmaybeiffalse) = post.getMutIf();
                if postmaybeiffalse.is_some() { continue }
                let postfvalue = if let mast!(Binary(is!("=="), Binary(is!("|"), Name(is!("label")), Num(0f64)), Num(n))) = *postcond { n } else { continue };
                let postvalue = f64toi32(postfvalue);
                // RSTODO: is it ok to blindly unwrap and assume the keys exist?
                if *labelAssigns.get(&postvalue).unwrap() != 1 || *labelChecks.get(&postvalue).unwrap() != 1 { continue }
                let prestats = if let Block(ref mut s) = **preiffalse { s } else { continue };
                let prestat = if prestats.len() == 1 { &mut prestats[0] } else { continue };
                let prefvalue = if let mast!(Stat(Assign(true, Name(is!("label")), Num(n)))) = *prestat { n } else { continue };
                // RSTODO: curiously, c++ doesn't do the conversion to int before comparing
                let prevalue = f64toi32(prefvalue);
                if prevalue != postvalue { continue }
                // Conditions match, just need to make sure the post clears label
                // RSTODO: the following two lines could be one if rust supported vec destructuring
                // RSTODO: note that this does not continue if poststats.len() == 0 (unlike C++), as I believe it's a valid joining - check with azakai
                let poststats = if let Block(ref mut s) = **postiftrue { s } else { continue };
                let haveclear = if let mast!(&[Stat(Assign(true, Name(is!("label")), Num(0f64))), ..]) = poststats.as_slice() { true } else { false };
                if inLoop.get() > 0 && !haveclear { continue }
                // Everything lines up, do it
                if haveclear { poststats.remove(0); } // remove the label clearing
                }
                let (_, postiftrue, _) = stats.remove(i+1).intoIf(); // remove the post entirely
                let (_, _, maybeiffalse) = stats[i].getMutIf();
                *maybeiffalse = Some(postiftrue);
                i += 1;
            }}
        }, |node: &mut AstValue| {
            if let While(..) = *node { inLoop.set(inLoop.get() - 1) }
        });
        assert!(inLoop.get() == 0);
    }

    })
}

// RSTODO: untested because I couldn't find anything to test it on. Maybe
// the emscripten test suite?
pub fn optimizeFrounds(ast: &mut AstValue) {
    // collapse fround(fround(..)), which can happen due to elimination
    // also emit f0 instead of fround(0) (except in returns)
    // RSTODO: could be a bool?
    let inReturn = Cell::new(0isize);
    traversePrePostMut(ast, |node: &mut AstValue| {
        if node.isReturn() { inReturn.set(inReturn.get() + 1) }
    }, |node: &mut AstValue| {
        match *node {
            Return(_) => inReturn.set(inReturn.get() - 1),
            Call(mast!(Name(is!("Math_fround"))), _) => {
                let maybenewnode;
                {
                let (_, args) = node.getMutCall();
                // RSTODO: valid assertion?
                assert!(args.len() == 1);
                let arg = &mut args[0];
                maybenewnode = match **arg {
                    Num(0f64) if inReturn.get() == 0 => Some(makeName(is!("f0"))),
                    Call(mast!(Name(is!("Math_fround"))), _) => Some(mem::replace(arg, makeEmpty())),
                    _ => None,
                }
                }
                if let Some(newnode) = maybenewnode {
                    *node = *newnode
                }
            },
            _ => (),
        }
    });
    // RSTODO: valid assertion?
    assert!(inReturn.get() == 0)
}

// RSTODO
//// Very simple 'registerization', coalescing of variables into a smaller number.
//
//const char* getRegPrefix(AsmType type) {
//  switch (type) {
//    case ASM_INT:       return "i"; break;
//    case ASM_DOUBLE:    return "d"; break;
//    case ASM_FLOAT:     return "f"; break;
//    case ASM_FLOAT32X4: return "F4"; break;
//    case ASM_FLOAT64X2: return "F2"; break;
//    case ASM_INT8X16:   return "I16"; break;
//    case ASM_INT16X8:   return "I8"; break;
//    case ASM_INT32X4:   return "I4"; break;
//    case ASM_BOOL8X16:  return "B16"; break;
//    case ASM_BOOL16X8:  return "B8"; break;
//    case ASM_BOOL32X4:  return "B4"; break;
//    case ASM_BOOL64X2:  return "B2"; break;
//    case ASM_NONE:      return "Z"; break;
//    default: assert(0); // type doesn't have a name yet
//  }
//  return nullptr;
//}
//
//IString getRegName(AsmType type, int num) {
//  const char* str = getRegPrefix(type);
//  const int size = 256;
//  char temp[size];
//  int written = sprintf(temp, "%s%d", str, num);
//  assert(written < size);
//  temp[written] = 0;
//  IString ret;
//  ret.set(temp, false);
//  return ret;
//}
//
//void registerize(Ref ast) {
//  traverseFunctions(ast, [](Ref fun) {
//    AsmData asmData(fun);
//    // Add parameters as a first (fake) var (with assignment), so they get taken into consideration
//    // note: params are special, they can never share a register between them (see later)
//    Ref fake;
//    if (!!fun[2] && fun[2]->size()) {
//      Ref assign = makeNum(0);
//      // TODO: will be an isEmpty here, can reuse it.
//      fun[3]->insert(0, make1(VAR, fun[2]->map([&assign](Ref param) {
//        return &(makeArray(2)->push_back(param).push_back(assign));
//      })));
//    }
//    // Replace all var definitions with assignments; we will add var definitions at the top after we registerize
//    StringSet allVars;
//    traversePre(fun, [&](Ref node) {
//      Ref type = node[0];
//      if (type == VAR) {
//        Ref vars = node[1]->filter([](Ref varr) { return varr->size() > 1; });
//        if (vars->size() >= 1) {
//          safeCopy(node, unVarify(vars));
//        } else {
//          safeCopy(node, makeEmpty());
//        }
//      } else if (type == NAME) {
//        allVars.insert(node[1]->getIString());
//      }
//    });
//    removeAllUselessSubNodes(fun); // vacuum?
//    StringTypeMap regTypes; // reg name -> type
//    auto getNewRegName = [&](int num, IString name) {
//      AsmType type = asmData.getType(name);
//      IString ret = getRegName(type, num);
//      assert(!allVars.has(ret) || asmData.isLocal(ret)); // register must not shadow non-local name
//      regTypes[ret] = type;
//      return ret;
//    };
//    // Find the # of uses of each variable.
//    // While doing so, check if all a variable's uses are dominated in a simple
//    // way by a simple assign, if so, then we can assign its register to it
//    // just for its definition to its last use, and not to the entire toplevel loop,
//    // we call such variables "optimizable"
//    StringIntMap varUses;
//    int level = 1;
//    std::unordered_map<int, StringSet> levelDominations; // level => set of dominated variables XXX vector?
//    StringIntMap varLevels;
//    StringSet possibles;
//    StringSet unoptimizables;
//    auto purgeLevel = [&]() {
//      // Invalidate all dominating on this level, further users make it unoptimizable
//      for (auto name : levelDominations[level]) {
//        varLevels[name] = 0;
//      }
//      levelDominations[level].clear();
//      level--;
//    };
//    std::function<bool (Ref node)> possibilifier = [&](Ref node) {
//      Ref type = node[0];
//      if (type == NAME) {
//        IString name = node[1]->getIString();
//        if (asmData.isLocal(name)) {
//          varUses[name]++;
//          if (possibles.has(name) && !varLevels[name]) unoptimizables.insert(name); // used outside of simple domination
//        }
//      } else if (type == ASSIGN && node[1]->isBool(true)) {
//        if (!!node[2] && node[2][0] == NAME) {
//          IString name = node[2][1]->getIString();
//          // if local and not yet used, this might be optimizable if we dominate
//          // all other uses
//          if (asmData.isLocal(name) && !varUses[name] && !varLevels[name]) {
//            possibles.insert(name);
//            varLevels[name] = level;
//            levelDominations[level].insert(name);
//          }
//        }
//      } else if (CONTROL_FLOW.has(type)) {
//        // recurse children, in the context of a loop
//        if (type == WHILE || type == DO) {
//          traversePrePostConditional(node[1], possibilifier, [](Ref node){});
//          level++;
//          traversePrePostConditional(node[2], possibilifier, [](Ref node){});
//          purgeLevel();
//        } else if (type == FOR) {
//          traversePrePostConditional(node[1], possibilifier, [](Ref node){});
//          for (int i = 2; i <= 4; i++) {
//            level++;
//            traversePrePostConditional(node[i], possibilifier, [](Ref node){});
//            purgeLevel();
//          }
//        } else if (type == IF) {
//          traversePrePostConditional(node[1], possibilifier, [](Ref node){});
//          level++;
//          traversePrePostConditional(node[2], possibilifier, [](Ref node){});
//          purgeLevel();
//          if (node->size() > 3 && !!node[3]) {
//            level++;
//            traversePrePostConditional(node[3], possibilifier, [](Ref node){});
//            purgeLevel();
//          }
//        } else if (type == SWITCH) {
//          traversePrePostConditional(node[1], possibilifier, [](Ref node){});
//          Ref cases = node[2];
//          for (size_t i = 0; i < cases->size(); i++) {
//            level++;
//            traversePrePostConditional(cases[i][1], possibilifier, [](Ref node){});
//            purgeLevel();
//          }
//        } else assert(0);;
//        return false; // prevent recursion into children, which we already did
//      }
//      return true;
//    };
//    traversePrePostConditional(fun, possibilifier, [](Ref node){});
//
//    StringSet optimizables;
//    for (auto possible : possibles) {
//      if (!unoptimizables.has(possible)) optimizables.insert(possible);
//    }
//
//    // Go through the function's code, assigning 'registers'.
//    // The only tricky bit is to keep variables locked on a register through loops,
//    // since they can potentially be returned to. Optimizable variables lock onto
//    // loops that they enter, unoptimizable variables lock in a conservative way
//    // into the topmost loop.
//    // Note that we cannot lock onto a variable in a loop if it was used and free'd
//    // before! (then they could overwrite us in the early part of the loop). For now
//    // we just use a fresh register to make sure we avoid this, but it could be
//    // optimized to check for safe registers (free, and not used in this loop level).
//    StringStringMap varRegs; // maps variables to the register they will use all their life
//    std::vector<StringVec> freeRegsClasses;
//    freeRegsClasses.resize(ASM_NONE);
//    int nextReg = 1;
//    StringVec fullNames;
//    fullNames.push_back(EMPTY); // names start at 1
//    std::vector<StringVec> loopRegs; // for each loop nesting level, the list of bound variables
//    int loops = 0; // 0 is toplevel, 1 is first loop, etc
//    StringSet activeOptimizables;
//    StringIntMap optimizableLoops;
//    StringSet paramRegs; // true if the register is used by a parameter (and so needs no def at start of function; also cannot
//                         // be shared with another param, each needs its own)
//    auto decUse = [&](IString name) {
//      if (!varUses[name]) return false; // no uses left, or not a relevant variable
//      if (optimizables.has(name)) activeOptimizables.insert(name);
//      IString reg = varRegs[name];
//      assert(asmData.isLocal(name));
//      StringVec& freeRegs = freeRegsClasses[asmData.getType(name)];
//      if (!reg) {
          //assert!(*reg != is!(""))
//        // acquire register
//        if (optimizables.has(name) && freeRegs.size() > 0 &&
//            !(asmData.isParam(name) && paramRegs.has(freeRegs.back()))) { // do not share registers between parameters
//          reg = freeRegs.back();
//          freeRegs.pop_back();
//        } else {
//          assert(fullNames.size() == nextReg);
//          reg = getNewRegName(nextReg++, name);
//          fullNames.push_back(reg);
//          if (asmData.isParam(name)) paramRegs.insert(reg);
//        }
//        varRegs[name] = reg;
//      }
//      varUses[name]--;
//      assert(varUses[name] >= 0);
//      if (varUses[name] == 0) {
//        if (optimizables.has(name)) activeOptimizables.erase(name);
//        // If we are not in a loop, or we are optimizable and not bound to a loop
//        // (we might have been in one but left it), we can free the register now.
//        if (loops == 0 || (optimizables.has(name) && !optimizableLoops.has(name))) {
//          // free register
//          freeRegs.push_back(reg);
//        } else {
//          // when the relevant loop is exited, we will free the register
//          int relevantLoop = optimizables.has(name) ? (optimizableLoops[name] ? optimizableLoops[name] : 1) : 1;
//          if ((int)loopRegs.size() <= relevantLoop+1) loopRegs.resize(relevantLoop+1);
//          loopRegs[relevantLoop].push_back(reg);
//        }
//      }
//      return true;
//    };
//    traversePrePost(fun, [&](Ref node) { // XXX we rely on traversal order being the same as execution order here
//      Ref type = node[0];
//      if (type == NAME) {
//        IString name = node[1]->getIString();
//        if (decUse(name)) {
//          node[1]->setString(varRegs[name]);
//        }
//      } else if (LOOP.has(type)) {
//        loops++;
//        // Active optimizables lock onto this loop, if not locked onto one that encloses this one
//        for (auto name : activeOptimizables) {
//          if (!optimizableLoops[name]) {
//            optimizableLoops[name] = loops;
//          }
//        }
//      }
//    }, [&](Ref node) {
//      Ref type = node[0];
//      if (LOOP.has(type)) {
//        // Free registers that were locked to this loop
//        if ((int)loopRegs.size() > loops && loopRegs[loops].size() > 0) {
//          for (auto loopReg : loopRegs[loops]) {
//            freeRegsClasses[regTypes[loopReg]].push_back(loopReg);
//          }
//          loopRegs[loops].clear();
//        }
//        loops--;
//      }
//    });
//    if (!!fun[2] && fun[2]->size()) {
//      fun[2]->setSize(0); // clear params, we will fill with registers
//      fun[3]->splice(0, 1); // remove fake initial var
//    }
//
//    asmData.locals.clear();
//    asmData.params.clear();
//    asmData.vars.clear();
//    for (int i = 1; i < nextReg; i++) {
//      IString reg = fullNames[i];
//      AsmType type = regTypes[reg];
//      if (!paramRegs.has(reg)) {
//        asmData.addVar(reg, type);
//      } else {
//        asmData.addParam(reg, type);
//        fun[2]->push_back(makeString(reg));
//      }
//    }
//    asmData.denormalize();
//  });
//}
//
//// Assign variables to 'registers', coalescing them onto a smaller number of shared
//// variables.
////
//// This does the same job as 'registerize' above, but burns a lot more cycles trying
//// to reduce the total number of register variables.  Key points about the operation:
////
////   * we decompose the AST into a flow graph and perform a full liveness
////     analysis, to determine which variables are live at each point.
////
////   * variables that are live concurrently are assigned to different registers.
////
////   * variables that are linked via 'x=y' style statements are assigned the same
////     register if possible, so that the redundant assignment can be removed.
////     (e.g. assignments used to pass state around through loops).
////
////   * any code that cannot be reached through the flow-graph is removed.
////     (e.g. redundant break statements like 'break L123; break;').
////
////   * any assignments that we can prove are not subsequently used are removed.
////     (e.g. unnecessary assignments to the 'label' variable).
////
//void registerizeHarder(Ref ast) {
//#ifdef PROFILING
//  clock_t tasmdata = 0;
//  clock_t tflowgraph = 0;
//  clock_t tlabelfix = 0;
//  clock_t tbackflow = 0;
//  clock_t tjuncvaruniqassign = 0;
//  clock_t tjuncvarsort = 0;
//  clock_t tregassign = 0;
//  clock_t tblockproc = 0;
//  clock_t treconstruct = 0;
//#endif
//
//  traverseFunctions(ast, [&](Ref fun) {
//
//#ifdef PROFILING
//    clock_t start = clock();
//#endif
//
//    // Do not try to process non-validating methods, like the heap replacer
//    bool abort = false;
//    traversePre(fun, [&abort](Ref node) {
//      if (node[0] == NEW) abort = true;
//    });
//    if (abort) return;
//
//    AsmData asmData(fun);
//
//#ifdef PROFILING
//    tasmdata += clock() - start;
//    start = clock();
//#endif
//
//    // Utilities for allocating register variables.
//    // We need distinct register pools for each type of variable.
//
//    typedef std::map<int, IString> IntStringMap;
//    std::vector<IntStringMap> allRegsByType;
//    allRegsByType.resize(ASM_NONE+1);
//    int nextReg = 1;
//
//    auto createReg = [&](IString forName) {
//      // Create a new register of type suitable for the given variable name.
//      AsmType type = asmData.getType(forName);
//      IntStringMap& allRegs = allRegsByType[type];
//      int reg = nextReg++;
//      allRegs[reg] = getRegName(type, reg);
//      return reg;
//    };
//
//    // Traverse the tree in execution order and synthesize a basic flow-graph.
//    // It's convenient to build a kind of "dual" graph where the nodes identify
//    // the junctions between blocks at which control-flow may branch, and each
//    // basic block is an edge connecting two such junctions.
//    // For each junction we store:
//    //    * set of blocks that originate at the junction
//    //    * set of blocks that terminate at the junction
//    // For each block we store:
//    //    * a single entry junction
//    //    * a single exit junction
//    //    * a 'use' and 'kill' set of names for the block
//    //    * full sequence of NAME and ASSIGN nodes in the block
//    //    * whether each such node appears as part of a larger expression
//    //      (and therefore cannot be safely eliminated)
//    //    * set of labels that can be used to jump to this block
//
//    struct Junction {
//      int id;
//      std::set<int> inblocks, outblocks;
//      IOrderedStringSet live;
//      Junction(int id_) : id(id_) {}
//    };
//    struct Node {
//    };
//    struct Block {
//      int id, entry, exit;
//      std::set<int> labels;
//      std::vector<Ref> nodes;
//      std::vector<bool> isexpr;
//      StringIntMap use;
//      StringSet kill;
//      StringStringMap link;
//      StringIntMap lastUseLoc;
//      StringIntMap firstDeadLoc;
//      StringIntMap firstKillLoc;
//      StringIntMap lastKillLoc;
//
//      Block() : id(-1), entry(-1), exit(-1) {}
//    };
//    struct ContinueBreak {
//      int co, br;
//      ContinueBreak() : co(-1), br(-1) {}
//      ContinueBreak(int co_, int br_) : co(co_), br(br_) {}
//    };
//    typedef std::unordered_map<IString, ContinueBreak> LabelState;
//
//    std::vector<Junction> junctions;
//    std::vector<Block*> blocks;
//    int currEntryJunction = -1;
//    Block* nextBasicBlock = nullptr;
//    int isInExpr = 0;
//    std::vector<LabelState> activeLabels;
//    activeLabels.resize(1);
//    IString nextLoopLabel;
//
//    const int ENTRY_JUNCTION = 0;
//    const int EXIT_JUNCTION = 1;
//    const int ENTRY_BLOCK = 0;
//
//    auto addJunction = [&]() {
//      // Create a new junction, without inserting it into the graph.
//      // This is useful for e.g. pre-allocating an exit node.
//      int id = junctions.size();
//      junctions.push_back(Junction(id));
//      return id;
//    };
//
//    std::function<int (int, bool)> joinJunction;
//
//    auto markJunction = [&](int id) {
//      // Mark current traversal location as a junction.
//      // This makes a new basic block exiting at this position.
//      if (id < 0) {
//        id = addJunction();
//      }
//      joinJunction(id, true);
//      return id;
//    };
//
//    auto setJunction = [&](int id, bool force) {
//      // Set the next entry junction to the given id.
//      // This can be used to enter at a previously-declared point.
//      // You can't return to a junction with no incoming blocks
//      // unless the 'force' parameter is specified.
//      assert(nextBasicBlock->nodes.size() == 0); // refusing to abandon an in-progress basic block
//      if (force || junctions[id].inblocks.size() > 0) {
//        currEntryJunction = id;
//      } else {
//        currEntryJunction = -1;
//      }
//    };
//
//    joinJunction = [&](int id, bool force) {
//      // Complete the pending basic block by exiting at this position.
//      // This can be used to exit at a previously-declared point.
//      if (currEntryJunction >= 0) {
//        assert(nextBasicBlock);
//        nextBasicBlock->id = blocks.size();
//        nextBasicBlock->entry = currEntryJunction;
//        nextBasicBlock->exit = id;
//        junctions[currEntryJunction].outblocks.insert(nextBasicBlock->id);
//        junctions[id].inblocks.insert(nextBasicBlock->id);
//        blocks.push_back(nextBasicBlock);
//      } 
//      nextBasicBlock = new Block();
//      setJunction(id, force);
//      return id;
//    };
//
//    auto pushActiveLabels = [&](int onContinue, int onBreak) {
//      // Push the target junctions for continuing/breaking a loop.
//      // This should be called before traversing into a loop.
//      assert(activeLabels.size() > 0);
//      LabelState& prevLabels = activeLabels.back();
//      LabelState newLabels = prevLabels;
//      newLabels[EMPTY] = ContinueBreak(onContinue, onBreak);
//      if (!!nextLoopLabel) {
          //assert!(*reg != is!(""))
//        newLabels[nextLoopLabel] = ContinueBreak(onContinue, onBreak);
          //Actually make this an option
//        nextLoopLabel = EMPTY;
//      }
//      // An unlabelled CONTINUE should jump to innermost loop,
//      // ignoring any nested SWITCH statements.
//      if (onContinue < 0 && prevLabels.count(EMPTY) > 0) {
//        newLabels[EMPTY].co = prevLabels[EMPTY].co;
//      }
//      activeLabels.push_back(newLabels);
//    };
//
//    auto popActiveLabels = [&]() {
//      // Pop the target junctions for continuing/breaking a loop.
//      // This should be called after traversing into a loop.
//      activeLabels.pop_back();
//    };
//
//    auto markNonLocalJump = [&](IString type, IString label) {
//      // Complete a block via RETURN, BREAK or CONTINUE.
//      // This joins the targetted junction and then sets the current junction to null.
//      // Any code traversed before we get back to an existing junction is dead code.
//      if (type == RETURN) {
//        joinJunction(EXIT_JUNCTION, false);
//      } else {
//        assert(activeLabels.size() > 0);
//        assert(activeLabels.back().count(label) > 0); // 'jump to unknown label');
//        auto targets = activeLabels.back()[label];
//        if (type == CONTINUE) {
//          joinJunction(targets.co, false);
//        } else if (type == BREAK) {
//          joinJunction(targets.br, false);
//        } else {
//          assert(0); // 'unknown jump node type');
//        }
//      }
//      currEntryJunction = -1;
//    };
//
//    auto addUseNode = [&](Ref node) {
//      // Mark a use of the given name node in the current basic block.
//      assert(node[0] == NAME); // 'not a use node');
//      IString name = node[1]->getIString();
//      if (asmData.isLocal(name)) {
//        nextBasicBlock->nodes.push_back(node);
//        nextBasicBlock->isexpr.push_back(isInExpr != 0);
//        if (nextBasicBlock->kill.count(name) == 0) {
//          nextBasicBlock->use[name] = 1;
//        }
//      }
//    };
//
//    auto addKillNode = [&](Ref node) {
//      // Mark an assignment to the given name node in the current basic block.
//      assert(node[0] == ASSIGN); //, 'not a kill node');
//      assert(node[1]->isBool(true)); // 'not a kill node');
//      assert(node[2][0] == NAME); //, 'not a kill node');
//      IString name = node[2][1]->getIString();
//      if (asmData.isLocal(name)) {
//        nextBasicBlock->nodes.push_back(node);
//        nextBasicBlock->isexpr.push_back(isInExpr != 0);
//        nextBasicBlock->kill.insert(name);
//      }
//    };
//
//    std::function<Ref (Ref)> lookThroughCasts = [&](Ref node) {
//      // Look through value-preserving casts, like "x | 0" => "x"
//      if (node[0] == BINARY && node[1] == OR) {
//        if (node[3][0] == NUM && node[3][1]->getNumber() == 0) {
//          return lookThroughCasts(node[2]);
//        }
//      }
//      return node;
//    };
//
//    auto addBlockLabel = [&](Ref node) {
//      assert(nextBasicBlock->nodes.size() == 0); // 'cant add label to an in-progress basic block')
//      if (node[0] == NUM) {
//        nextBasicBlock->labels.insert(node[1]->getInteger());
//      }
//    };
//
//    auto isTrueNode = [&](Ref node) {
//      // Check if the given node is statically truthy.
//      return (node[0] == NUM && node[1]->getNumber() != 0);
//    };
//
//    auto isFalseNode = [&](Ref node) {
//      // Check if the given node is statically falsy.
//      return (node[0] == NUM && node[1]->getNumber() == 0);
//    };
//
//    std::function<void (Ref)> buildFlowGraph = [&](Ref node) {
//      // Recursive function to build up the flow-graph.
//      // It walks the tree in execution order, calling the above state-management
//      // functions at appropriate points in the traversal.
//      Ref type = node[0];
//  
//      // Any code traversed without an active entry junction must be dead,
//      // as the resulting block could never be entered. Let's remove it.
//      if (currEntryJunction < 0 && junctions.size() > 0) {
//        safeCopy(node, makeEmpty());
//        return;
//      }
// 
//      // Traverse each node type according to its particular control-flow semantics.
//      // TODO: switchify this
//      if (type == DEFUN) {
//        int jEntry = markJunction(-1);
//        assert(jEntry == ENTRY_JUNCTION);
//        int jExit = addJunction();
//        assert(jExit == EXIT_JUNCTION);
//        for (size_t i = 0; i < node[3]->size(); i++) {
//          buildFlowGraph(node[3][i]);
//        }
//        joinJunction(jExit, false);
//      } else if (type == IF) {
//        isInExpr++;
//        buildFlowGraph(node[1]);
//        isInExpr--;
//        int jEnter = markJunction(-1);
//        int jExit = addJunction();
//        if (!!node[2]) {
//          // Detect and mark "if (label == N) { <labelled block> }".
//          if (node[1][0] == BINARY && node[1][1] == EQ) {
//            Ref lhs = lookThroughCasts(node[1][2]);
//            if (lhs[0] == NAME && lhs[1] == LABEL) {
//              addBlockLabel(lookThroughCasts(node[1][3]));
//            }
//          }
//          buildFlowGraph(node[2]);
//        }
//        joinJunction(jExit, false);
//        setJunction(jEnter, false);
//        if (node->size() > 3 && !!node[3]) {
//          buildFlowGraph(node[3]);
//        }
//        joinJunction(jExit, false);
//      } else if (type == CONDITIONAL) {
//        isInExpr++;
//        // If the conditional has no side-effects, we can treat it as a single
//        // block, which might open up opportunities to remove it entirely.
//        if (!hasSideEffects(node)) {
//          buildFlowGraph(node[1]);
//          if (!!node[2]) {
//            buildFlowGraph(node[2]);
//          }
//          if (!!node[3]) {
//            buildFlowGraph(node[3]);
//          }
//        } else {
//          buildFlowGraph(node[1]);
//          int jEnter = markJunction(-1);
//          int jExit = addJunction();
//          if (!!node[2]) {
//            buildFlowGraph(node[2]);
//          }
//          joinJunction(jExit, false);
//          setJunction(jEnter, false);
//          if (!!node[3]) {
//            buildFlowGraph(node[3]);
//          }
//          joinJunction(jExit, false);
//        }
//        isInExpr--;
//      } else if (type == WHILE) {
//        // Special-case "while (1) {}" to use fewer junctions,
//        // since emscripten generates a lot of these.
//        if (isTrueNode(node[1])) {
//          int jLoop = markJunction(-1);
//          int jExit = addJunction();
//          pushActiveLabels(jLoop, jExit);
//          buildFlowGraph(node[2]);
//          popActiveLabels();
//          joinJunction(jLoop, false);
//          setJunction(jExit, false);
//        } else {
//          int jCond = markJunction(-1);
//          int jLoop = addJunction();
//          int jExit = addJunction();
//          isInExpr++;
//          buildFlowGraph(node[1]);
//          isInExpr--;
//          joinJunction(jLoop, false);
//          pushActiveLabels(jCond, jExit);
//          buildFlowGraph(node[2]);
//          popActiveLabels();
//          joinJunction(jCond, false);
//          // An empty basic-block linking condition exit to loop exit.
//          setJunction(jLoop, false);
//          joinJunction(jExit, false);
//        }
//      } else if (type == DO) {
//        // Special-case "do {} while (1)" and "do {} while (0)" to use
//        // fewer junctions, since emscripten generates a lot of these.
//        if (isFalseNode(node[1])) {
//          int jExit = addJunction();
//          pushActiveLabels(jExit, jExit);
//          buildFlowGraph(node[2]);
//          popActiveLabels();
//          joinJunction(jExit, false);
//        } else if (isTrueNode(node[1])) {
//          int jLoop = markJunction(-1);
//          int jExit = addJunction();
//          pushActiveLabels(jLoop, jExit);
//          buildFlowGraph(node[2]);
//          popActiveLabels();
//          joinJunction(jLoop, false);
//          setJunction(jExit, false);
//        } else {
//          int jLoop = markJunction(-1);
//          int jCond = addJunction();
//          int jCondExit = addJunction();
//          int jExit = addJunction();
//          pushActiveLabels(jCond, jExit);
//          buildFlowGraph(node[2]);
//          popActiveLabels();
//          joinJunction(jCond, false);
//          isInExpr++;
//          buildFlowGraph(node[1]);
//          isInExpr--;
//          joinJunction(jCondExit, false);
//          joinJunction(jLoop, false);
//          setJunction(jCondExit, false);
//          joinJunction(jExit, false);
//        }
//      } else if (type == FOR) {
//        int jTest = addJunction();
//        int jBody = addJunction();
//        int jStep = addJunction();
//        int jExit = addJunction();
//        buildFlowGraph(node[1]);
//        joinJunction(jTest, false);
//        isInExpr++;
//        buildFlowGraph(node[2]);
//        isInExpr--;
//        joinJunction(jBody, false);
//        pushActiveLabels(jStep, jExit);
//        buildFlowGraph(node[4]);
//        popActiveLabels();
//        joinJunction(jStep, false);
//        buildFlowGraph(node[3]);
//        joinJunction(jTest, false);
//        setJunction(jBody, false);
//        joinJunction(jExit, false);
//      } else if (type == LABEL) {
//        assert(BREAK_CAPTURERS.has(node[2][0])); // 'label on non-loop, non-switch statement')
//        nextLoopLabel = node[1]->getIString();
//        buildFlowGraph(node[2]);
//      } else if (type == SWITCH) {
//        // Emscripten generates switch statements of a very limited
//        // form: all case clauses are numeric literals, and all
//        // case bodies end with a (maybe implicit) break.  So it's
//        // basically equivalent to a multi-way IF statement.
//        isInExpr++;
//        buildFlowGraph(node[1]);
//        isInExpr--;
//        Ref condition = lookThroughCasts(node[1]);
//        int jCheckExit = markJunction(-1);
//        int jExit = addJunction();
//        pushActiveLabels(-1, jExit);
//        bool hasDefault = false;
//        for (size_t i = 0; i < node[2]->size(); i++) {
//          setJunction(jCheckExit, false);
//          // All case clauses are either 'default' or a numeric literal.
//          if (!node[2][i][0]) {
//            hasDefault = true;
//          } else {
//            // Detect switches dispatching to labelled blocks.
//            if (condition[0] == NAME && condition[1] == LABEL) {
//              addBlockLabel(lookThroughCasts(node[2][i][0]));
//            }
//          }
//          for (size_t j = 0; j < node[2][i][1]->size(); j++) {
//            buildFlowGraph(node[2][i][1][j]);
//          }
//          // Control flow will never actually reach the end of the case body.
//          // If there's live code here, assume it jumps to case exit.
//          if (currEntryJunction >= 0 && nextBasicBlock->nodes.size() > 0) {
//            if (!!node[2][i][0]) {
//              markNonLocalJump(RETURN, EMPTY);
//            } else {
//              joinJunction(jExit, false);
//            }
//          }
//        }
//        // If there was no default case, we also need an empty block
//        // linking straight from the test evaluation to the exit.
//        if (!hasDefault) {
//          setJunction(jCheckExit, false);
//        }
//        joinJunction(jExit, false);
//        popActiveLabels();
//      } else if (type == RETURN) {
//        if (!!node[1]) {
//          isInExpr++;
//          buildFlowGraph(node[1]);
//          isInExpr--;
//        }
//        markNonLocalJump(type->getIString(), EMPTY);
//      } else if (type == BREAK || type == CONTINUE) {
//        markNonLocalJump(type->getIString(), !!node[1] ? node[1]->getIString() : EMPTY);
//      } else if (type == ASSIGN) {
//        isInExpr++;
//        buildFlowGraph(node[3]);
//        isInExpr--;
//        if (node[1]->isBool(true) && node[2][0] == NAME) {
//          addKillNode(node);
//        } else {
//          buildFlowGraph(node[2]);
//        }
//      } else if (type == NAME) {
//        addUseNode(node);
//      } else if (type == BLOCK || type == TOPLEVEL) {
//        if (!!node[1]) {
//          for (size_t i = 0; i < node[1]->size(); i++) {
//            buildFlowGraph(node[1][i]);
//          }
//        }
//      } else if (type == STAT) {
//        buildFlowGraph(node[1]);
//      } else if (type == UNARY_PREFIX || type == UNARY_POSTFIX) {
//        isInExpr++;
//        buildFlowGraph(node[2]);
//        isInExpr--;
//      } else if (type == BINARY) {
//        isInExpr++;
//        buildFlowGraph(node[2]);
//        buildFlowGraph(node[3]);
//        isInExpr--;
//      } else if (type == CALL) {
//        isInExpr++;
//        buildFlowGraph(node[1]);
//        if (!!node[2]) {
//          for (size_t i = 0; i < node[2]->size(); i++) {
//            buildFlowGraph(node[2][i]);
//          }
//        }
//        isInExpr--;
//        // If the call is statically known to throw,
//        // treat it as a jump to function exit.
//        if (!isInExpr && node[1][0] == NAME) {
//          if (FUNCTIONS_THAT_ALWAYS_THROW.has(node[1][1])) {
//            markNonLocalJump(RETURN, EMPTY);
//          }
//        }
//      } else if (type == SEQ || type == SUB) {
//        isInExpr++;
//        buildFlowGraph(node[1]);
//        buildFlowGraph(node[2]);
//        isInExpr--;
//      } else if (type == DOT || type == THROW) {
//        isInExpr++;
//        buildFlowGraph(node[1]);
//        isInExpr--;
//      } else if (type == NUM || type == STRING || type == VAR) {
//        // nada
//      } else {
//        assert(0); // 'unsupported node type: ' + type);
//      }
//    };
//
//    buildFlowGraph(fun);
//
//#ifdef PROFILING
//    tflowgraph += clock() - start;
//    start = clock();
//#endif
//
//    assert(junctions[ENTRY_JUNCTION].inblocks.size() == 0); // 'function entry must have no incoming blocks');
//    assert(junctions[EXIT_JUNCTION].outblocks.size() == 0); // 'function exit must have no outgoing blocks');
//    assert(blocks[ENTRY_BLOCK]->entry == ENTRY_JUNCTION); //, 'block zero must be the initial block');
//
//    // Fix up implicit jumps done by assigning to the LABEL variable.
//    // If a block ends with an assignment to LABEL and there's another block
//    // with that value of LABEL as precondition, we tweak the flow graph so
//    // that the former jumps straight to the later.
//
//    std::map<int, Block*> labelledBlocks;
//    typedef std::pair<Ref, Block*> Jump;
//    std::vector<Jump> labelledJumps;
//
//    for (size_t i = 0; i < blocks.size(); i++) {
//      Block* block = blocks[i];
//      // Does it have any labels as preconditions to its entry?
//      for (auto labelVal : block->labels) {
//        // If there are multiple blocks with the same label, all bets are off.
//        // This seems to happen sometimes for short blocks that end with a return.
//        // TODO: it should be safe to merge the duplicates if they're identical.
//        if (labelledBlocks.count(labelVal) > 0) {
//          labelledBlocks.clear();
//          labelledJumps.clear();
//          goto AFTER_FINDLABELLEDBLOCKS;
//        }
//        labelledBlocks[labelVal] = block;
//      }
//      // Does it assign a specific label value at exit?
//      if (block->kill.has(LABEL)) {
//        Ref finalNode = block->nodes.back();
//        if (finalNode[0] == ASSIGN && finalNode[2][1] == LABEL) {
//          // If labels are computed dynamically then all bets are off.
//          // This can happen due to indirect branching in llvm output.
//          if (finalNode[3][0] != NUM) {
//            labelledBlocks.clear();
//            labelledJumps.clear();
//            goto AFTER_FINDLABELLEDBLOCKS;
//          }
//          labelledJumps.push_back(Jump(finalNode[3][1], block));
//        } else { 
//          // If label is assigned a non-zero value elsewhere in the block
//          // then all bets are off.  This can happen e.g. due to outlining
//          // saving/restoring label to the stack.
//          for (size_t j = 0; j < block->nodes.size() - 1; j++) {
//            if (block->nodes[j][0] == ASSIGN && block->nodes[j][2][1] == LABEL) {
//              if (block->nodes[j][3][0] != NUM || block->nodes[j][3][1]->getNumber() != 0) {
//                labelledBlocks.clear();
//                labelledJumps.clear();
//                goto AFTER_FINDLABELLEDBLOCKS;
//              }
//            }
//          }
//        }
//      }
//    }
//
//    AFTER_FINDLABELLEDBLOCKS:
//
//    for (auto labelVal : labelledBlocks) {
//      Block* block = labelVal.second;
//      // Disconnect it from the graph, and create a
//      // new junction for jumps targetting this label.
//      junctions[block->entry].outblocks.erase(block->id);
//      block->entry = addJunction();
//      junctions[block->entry].outblocks.insert(block->id);
//      // Add a fake use of LABEL to keep it alive in predecessor.
//      block->use[LABEL] = 1;
//      block->nodes.insert(block->nodes.begin(), makeName(LABEL));
//      block->isexpr.insert(block->isexpr.begin(), 1);
//    }
//    for (size_t i = 0; i < labelledJumps.size(); i++) {
//      auto labelVal = labelledJumps[i].first;
//      auto block = labelledJumps[i].second;
//      Block* targetBlock = labelledBlocks[labelVal->getInteger()];
//      if (targetBlock) {
//        // Redirect its exit to entry of the target block.
//        junctions[block->exit].inblocks.erase(block->id);
//        block->exit = targetBlock->entry;
//        junctions[block->exit].inblocks.insert(block->id);
//      }
//    }
//
//#ifdef PROFILING
//    tlabelfix += clock() - start;
//    start = clock();
//#endif
//
//    // Do a backwards data-flow analysis to determine the set of live
//    // variables at each junction, and to use this information to eliminate
//    // any unused assignments.
//    // We run two nested phases.  The inner phase builds the live set for each
//    // junction.  The outer phase uses this to try to eliminate redundant
//    // stores in each basic block, which might in turn affect liveness info.
//
//    auto analyzeJunction = [&](Junction& junc) {
//      // Update the live set for this junction.
//      IOrderedStringSet live;
//      for (auto b : junc.outblocks) {
//        Block* block = blocks[b];
//        IOrderedStringSet& liveSucc = junctions[block->exit].live;
//        for (auto name : liveSucc) {
//          if (!block->kill.has(name)) {
//            live.insert(name);
//          }
//        }
//        for (auto name : block->use) {
//          live.insert(name.first);
//        }
//      }
//      junc.live = live;
//    };
//
//    auto analyzeBlock = [&](Block* block) {
//      // Update information about the behaviour of the block.
//      // This includes the standard 'use' and 'kill' information,
//      // plus a 'link' set naming values that flow through from entry
//      // to exit, possibly changing names via simple 'x=y' assignments.
//      // As we go, we eliminate assignments if the variable is not
//      // subsequently used.
//      auto live = junctions[block->exit].live;
//      StringIntMap use;
//      StringSet kill;
//      StringStringMap link;
//      StringIntMap lastUseLoc;
//      StringIntMap firstDeadLoc;
//      StringIntMap firstKillLoc;
//      StringIntMap lastKillLoc;
//      for (auto name : live) {
//        link[name] = name;
//        lastUseLoc[name] = block->nodes.size();
//        firstDeadLoc[name] = block->nodes.size();
//      }
//      for (int j = block->nodes.size() - 1; j >= 0 ; j--) {
//        Ref node = block->nodes[j];
//        if (node[0] == NAME) {
//          IString name = node[1]->getIString();
//          live.insert(name);
//          use[name] = j;
//          if (lastUseLoc.count(name) == 0) {
//            lastUseLoc[name] = j;
//            firstDeadLoc[name] = j;
//          }
//        } else {
//          IString name = node[2][1]->getIString();
//          // We only keep assignments if they will be subsequently used.
//          if (live.has(name)) {
//            kill.insert(name);
//            use.erase(name);
//            live.erase(name);
//            firstDeadLoc[name] = j;
//            firstKillLoc[name] = j;
//            if (lastUseLoc.count(name) == 0) {
//              lastUseLoc[name] = j;
//            }
//            if (lastKillLoc.count(name) == 0) {
//              lastKillLoc[name] = j;
//            }
//            // If it's an "x=y" and "y" is not live, then we can create a
//            // flow-through link from "y" to "x".  If not then there's no
//            // flow-through link for "x".
//            if (link.has(name)) {
//              IString oldLink = link[name];
//              link.erase(name);
//              if (node[3][0] == NAME) {
//                if (asmData.isLocal(node[3][1]->getIString())) {
//                  link[node[3][1]->getIString()] = oldLink;
//                }
//              }
//            }
//          } else {
//            // The result of this assignment is never used, so delete it.
//            // We may need to keep the RHS for its value or its side-effects.
//            auto removeUnusedNodes = [&](int j, int n) {
//              for (auto pair : lastUseLoc) {
//                pair.second -= n;
//              }
//              for (auto pair : firstKillLoc) {
//                pair.second -= n;
//              }
//              for (auto pair : lastKillLoc) {
//                pair.second -= n;
//              }
//              for (auto pair : firstDeadLoc) {
//                pair.second -= n;
//              }
//              block->nodes.erase(block->nodes.begin() + j, block->nodes.begin() + j + n);
//              block->isexpr.erase(block->isexpr.begin() + j, block->isexpr.begin() + j + n);
//            };
//            if (block->isexpr[j] || hasSideEffects(node[3])) {
//              safeCopy(node, node[3]);
//              removeUnusedNodes(j, 1);
//            } else {
//              int numUsesInExpr = 0;
//              traversePre(node[3], [&](Ref node) {
//                if (node[0] == NAME && asmData.isLocal(node[1]->getIString())) {
//                  numUsesInExpr++;
//                }
//              });
//              safeCopy(node, makeEmpty());
//              j = j - numUsesInExpr;
//              removeUnusedNodes(j, 1 + numUsesInExpr);
//            }
//          }
//        }
//      }
//      // XXX efficiency
//      block->use = use;
//      block->kill = kill;
//      block->link = link;
//      block->lastUseLoc = lastUseLoc;
//      block->firstDeadLoc = firstDeadLoc;
//      block->firstKillLoc = firstKillLoc;
//      block->lastKillLoc = lastKillLoc;
//    };
//
//    // Ordered map to work in approximate reverse order of junction appearance
//    std::set<int> jWorkSet;
//    std::set<int> bWorkSet;
//
//    // Be sure to visit every junction at least once.
//    // This avoids missing some vars because we disconnected them
//    // when processing the labelled jumps.
//    for (size_t i = EXIT_JUNCTION; i < junctions.size(); i++) {
//      jWorkSet.insert(i);
//      for (auto b : junctions[i].inblocks) {
//        bWorkSet.insert(b);
//      }
//    }
//    // Exit junction never has any live variable changes to propagate
//    jWorkSet.erase(EXIT_JUNCTION);
//
//    do {
//      // Iterate on just the junctions until we get stable live sets.
//      // The first run of this loop will grow the live sets to their maximal size.
//      // Subsequent runs will shrink them based on eliminated in-block uses.
//      while (jWorkSet.size() > 0) {
//        auto last = jWorkSet.end();
//        --last;
//        Junction& junc = junctions[*last];
//        jWorkSet.erase(last);
//        IOrderedStringSet oldLive = junc.live; // copy it here, to check for changes later
//        analyzeJunction(junc);
//        if (oldLive != junc.live) {
//          // Live set changed, updated predecessor blocks and junctions.
//          for (auto b : junc.inblocks) {
//            bWorkSet.insert(b);
//            jWorkSet.insert(blocks[b]->entry);
//          }
//        }
//      }
//      // Now update the blocks based on the calculated live sets.
//      while (bWorkSet.size() > 0) {
//        auto last = bWorkSet.end();
//        --last;
//        Block* block = blocks[*last];
//        bWorkSet.erase(last);
//        auto oldUse = block->use;
//        analyzeBlock(block);
//        if (oldUse != block->use) {
//          // The use set changed, re-process the entry junction.
//          jWorkSet.insert(block->entry);
//        }
//      }
//    } while (jWorkSet.size() > 0);
//
//#ifdef PROFILING
//    tbackflow += clock() - start;
//    start = clock();
//#endif
//
//    // Insist that all function parameters are alive at function entry.
//    // This ensures they will be assigned independent registers, even
//    // if they happen to be unused.
//
//    for (auto name : asmData.params) {
//      junctions[ENTRY_JUNCTION].live.insert(name);
//    }
//
//    // For variables that are live at one or more junctions, we assign them
//    // a consistent register for the entire scope of the function.  Find pairs
//    // of variable that cannot use the same register (the "conflicts") as well
//    // as pairs of variables that we'd like to have share the same register
//    // (the "links").
//
//    struct JuncVar {
//      std::vector<bool> conf;
//      IOrderedStringSet link;
//      std::unordered_set<int> excl;
//      int reg;
//      bool used;
//      JuncVar() : reg(-1), used(false) {}
//    };
//    size_t numLocals = asmData.locals.size();
//    std::unordered_map<IString, size_t> nameToNum;
//    std::vector<IString> numToName;
//    nameToNum.reserve(numLocals);
//    numToName.reserve(numLocals);
//    for (auto kv : asmData.locals) {
//      nameToNum[kv.first] = numToName.size();
//      numToName.push_back(kv.first);
//    }
//
//    std::vector<JuncVar> juncVars(numLocals);
//    for (Junction& junc : junctions) {
//      for (IString name : junc.live) {
//        JuncVar& jVar = juncVars[nameToNum[name]];
//        jVar.used = true;
//        jVar.conf.assign(numLocals, false);
//      }
//    }
//    std::map<IString, std::vector<Block*>> possibleBlockConflictsMap;
//    std::vector<std::pair<size_t, std::vector<Block*>>> possibleBlockConflicts;
//    std::unordered_map<IString, std::vector<Block*>> possibleBlockLinks;
//    possibleBlockConflicts.reserve(numLocals);
//    possibleBlockLinks.reserve(numLocals);
//
//    for (Junction& junc : junctions) {
//      // Pre-compute the possible conflicts and links for each block rather
//      // than checking potentially impossible options for each var
//      possibleBlockConflictsMap.clear();
//      possibleBlockConflicts.clear();
//      possibleBlockLinks.clear();
//      for (auto b : junc.outblocks) {
//        Block* block = blocks[b];
//        Junction& jSucc = junctions[block->exit];
//        for (auto name : jSucc.live) {
//          possibleBlockConflictsMap[name].push_back(block);
//        }
//        for (auto name_linkname : block->link) {
//          if (name_linkname.first != name_linkname.second) {
//            possibleBlockLinks[name_linkname.first].push_back(block);
//          }
//        }
//      }
//      // Find the live variables in this block, mark them as unnecessary to
//      // check for conflicts (we mark all live vars as conflicting later)
//      std::vector<size_t> liveJVarNums;
//      liveJVarNums.reserve(junc.live.size());
//      for (auto name : junc.live) {
//        size_t jVarNum = nameToNum[name];
//        liveJVarNums.push_back(jVarNum);
//        possibleBlockConflictsMap.erase(name);
//      }
//      // Extract just the variables we might want to check for conflicts
//      for (auto kv : possibleBlockConflictsMap) {
//        possibleBlockConflicts.push_back(std::make_pair(nameToNum[kv.first], kv.second));
//      }
//
//      for (size_t jVarNum : liveJVarNums) {
//        JuncVar& jvar = juncVars[jVarNum];
//        IString name = numToName[jVarNum];
//        // It conflicts with all other names live at this junction.
//        for (size_t liveJVarNum : liveJVarNums) {
//          jvar.conf[liveJVarNum] = true;
//        }
//        jvar.conf[jVarNum] = false; // except for itself, of course
//
//        // It conflicts with any output vars of successor blocks,
//        // if they're assigned before it goes dead in that block.
//        for (auto jvarnum_blocks : possibleBlockConflicts) {
//          size_t otherJVarNum = jvarnum_blocks.first;
//          IString otherName = numToName[otherJVarNum];
//          for (auto block : jvarnum_blocks.second) {
//            if (block->lastKillLoc[otherName] < block->firstDeadLoc[name]) {
//              jvar.conf[otherJVarNum] = true;
//              juncVars[otherJVarNum].conf[jVarNum] = true;
//              break;
//            }
//          }
//        }
//
//        // It links with any linkages in the outgoing blocks.
//        for (auto block: possibleBlockLinks[name]) {
//          IString linkName = block->link[name];
//          jvar.link.insert(linkName);
//          juncVars[nameToNum[linkName]].link.insert(name);
//        }
//      }
//    }
//
//#ifdef PROFILING
//    tjuncvaruniqassign += clock() - start;
//    start = clock();
//#endif
//
//    // Attempt to sort the junction variables to heuristically reduce conflicts.
//    // Simple starting point: handle the most-conflicted variables first.
//    // This seems to work pretty well.
//
//    std::vector<size_t> sortedJVarNums;
//    sortedJVarNums.reserve(juncVars.size());
//    std::vector<size_t> jVarConfCounts(numLocals);
//    for (size_t jVarNum = 0; jVarNum < juncVars.size(); jVarNum++) {
//      JuncVar& jVar = juncVars[jVarNum];
//      if (!jVar.used) continue;
//      jVarConfCounts[jVarNum] = std::count(jVar.conf.begin(), jVar.conf.end(), true);
//      sortedJVarNums.push_back(jVarNum);
//    }
//    std::sort(sortedJVarNums.begin(), sortedJVarNums.end(), [&](const size_t vi1, const size_t vi2) {
//      // sort by # of conflicts
//      if (jVarConfCounts[vi1] < jVarConfCounts[vi2]) return true;
//      if (jVarConfCounts[vi1] == jVarConfCounts[vi2]) return numToName[vi1] < numToName[vi2];
//      return false;
//    });
//
//#ifdef PROFILING
//    tjuncvarsort += clock() - start;
//    start = clock();
//#endif
//
//    // We can now assign a register to each junction variable.
//    // Process them in order, trying available registers until we find
//    // one that works, and propagating the choice to linked/conflicted
//    // variables as we go.
//
//    std::function<bool (IString, int)> tryAssignRegister = [&](IString name, int reg) {
//      // Try to assign the given register to the given variable,
//      // and propagate that choice throughout the graph.
//      // Returns true if successful, false if there was a conflict.
//      JuncVar& jv = juncVars[nameToNum[name]];
//      if (jv.reg > 0) {
//        return jv.reg == reg;
//      }
//      if (jv.excl.count(reg) > 0) {
//        return false;
//      }
//      jv.reg = reg;
//      // Exclude use of this register at all conflicting variables.
//      for (size_t confNameNum = 0; confNameNum < jv.conf.size(); confNameNum++) {
//        if (jv.conf[confNameNum]) {
//          juncVars[confNameNum].excl.insert(reg);
//        }
//      }
//      // Try to propagate it into linked variables.
//      // It's not an error if we can't.
//      for (auto linkName : jv.link) {
//        tryAssignRegister(linkName, reg);
//      }
//      return true;
//    };
//    for (size_t jVarNum : sortedJVarNums) {
//      // It may already be assigned due to linked-variable propagation.
//      if (juncVars[jVarNum].reg > 0) {
//        continue;
//      }
//      IString name = numToName[jVarNum];
//      // Try to use existing registers first.
//      auto& allRegs = allRegsByType[asmData.getType(name)];
//      bool moar = false;
//      for (auto reg : allRegs) {
//        if (tryAssignRegister(name, reg.first)) {
//          moar = true;
//          break;
//        }
//      }
//      if (moar) continue;
//      // They're all taken, create a new one.
//      tryAssignRegister(name, createReg(name));
//    }
//
//#ifdef PROFILING
//    tregassign += clock() - start;
//    start = clock();
//#endif
//
//    // Each basic block can now be processed in turn.
//    // There may be internal-use-only variables that still need a register
//    // assigned, but they can be treated just for this block.  We know
//    // that all inter-block variables are in a good state thanks to
//    // junction variable consistency.
//
//    for (size_t i = 0; i < blocks.size(); i++) {
//      Block* block = blocks[i];
//      if (block->nodes.size() == 0) continue;
//      Junction& jEnter = junctions[block->entry];
//      Junction& jExit = junctions[block->exit];
//      // Mark the point at which each input reg becomes dead.
//      // Variables alive before this point must not be assigned
//      // to that register.
//      StringSet inputVars;
//      std::unordered_map<int, int> inputDeadLoc;
//      std::unordered_map<int, IString> inputVarsByReg;
//      for (auto name : jExit.live) {
//        if (!block->kill.has(name)) {
//          inputVars.insert(name);
//          int reg = juncVars[nameToNum[name]].reg;
//          assert(reg > 0); // 'input variable doesnt have a register');
//          inputDeadLoc[reg] = block->firstDeadLoc[name];
//          inputVarsByReg[reg] = name;
//        }
//      }
//      for (auto pair : block->use) {
//        IString name = pair.first;
//        if (!inputVars.has(name)) {
//          inputVars.insert(name);
//          int reg = juncVars[nameToNum[name]].reg;
//          assert(reg > 0); // 'input variable doesnt have a register');
//          inputDeadLoc[reg] = block->firstDeadLoc[name];
//          inputVarsByReg[reg] = name;
//        }
//      }
//      // TODO assert(setSize(setSub(inputVars, jEnter.live)) == 0);
//      // Scan through backwards, allocating registers on demand.
//      // Be careful to avoid conflicts with the input registers.
//      // We consume free registers in last-used order, which helps to
//      // eliminate "x=y" assignments that are the last use of "y".
//      StringIntMap assignedRegs;
//      auto freeRegsByTypePre = allRegsByType; // XXX copy
//      // Begin with all live vars assigned per the exit junction.
//      for (auto name : jExit.live) {
//        int reg = juncVars[nameToNum[name]].reg;
//        assert(reg > 0); // 'output variable doesnt have a register');
//        assignedRegs[name] = reg;
//        freeRegsByTypePre[asmData.getType(name)].erase(reg); // XXX assert?
//      }
//      std::vector<std::vector<int>> freeRegsByType;
//      freeRegsByType.resize(freeRegsByTypePre.size());
//      for (size_t j = 0; j < freeRegsByTypePre.size(); j++) {
//        for (auto pair : freeRegsByTypePre[j]) {
//          freeRegsByType[j].push_back(pair.first);
//        }
//      }
//      // Scan through the nodes in sequence, modifying each node in-place
//      // and grabbing/freeing registers as needed.
//      std::vector<std::pair<int, Ref>> maybeRemoveNodes;
//      for (int j = block->nodes.size() - 1; j >= 0; j--) {
//        Ref node = block->nodes[j];
//        IString name = (node[0] == ASSIGN ? node[2][1] : node[1])->getIString();
//        IntStringMap& allRegs = allRegsByType[asmData.getType(name)];
//        std::vector<int>& freeRegs = freeRegsByType[asmData.getType(name)];
//        int reg = assignedRegs[name]; // XXX may insert a zero
//        if (node[0] == NAME) {
//          // A use.  Grab a register if it doesn't have one.
//          if (reg <= 0) {
//            if (inputVars.has(name) && j <= block->firstDeadLoc[name]) {
//              // Assignment to an input variable, must use pre-assigned reg.
//              reg = juncVars[nameToNum[name]].reg;
//              assignedRegs[name] = reg;
//              for (int k = freeRegs.size() - 1; k >= 0; k--) {
//                if (freeRegs[k] == reg) {
//                  freeRegs.erase(freeRegs.begin() + k);
//                  break;
//                }
//              }
//            } else {
//              // Try to use one of the existing free registers.
//              // It must not conflict with an input register.
//              for (int k = freeRegs.size() - 1; k >= 0; k--) {
//                reg = freeRegs[k];
//                // Check for conflict with input registers.
//                if (inputDeadLoc.count(reg) > 0) {
//                  if (block->firstKillLoc[name] <= inputDeadLoc[reg]) {
//                    if (name != inputVarsByReg[reg]) {
//                      continue;
//                    }
//                  }
//                }
//                // Found one!
//                assignedRegs[name] = reg;
//                assert(reg > 0);
//                freeRegs.erase(freeRegs.begin() + k);
//                break;
//              }
//              // If we didn't find a suitable register, create a new one.
//              if (assignedRegs[name] <= 0) {
//                reg = createReg(name);
//                assignedRegs[name] = reg;
//              }
//            }
//          }
//          node[1]->setString(allRegs[reg]);
//        } else {
//          // A kill. This frees the assigned register.
//          assert(reg > 0); //, 'live variable doesnt have a reg?')
//          node[2][1]->setString(allRegs[reg]);
//          freeRegs.push_back(reg);
//          assignedRegs.erase(name);
//          if (node[3][0] == NAME && asmData.isLocal(node[3][1]->getIString())) {
//            maybeRemoveNodes.push_back(std::pair<int, Ref>(j, node));
//          }
//        }
//      }
//      // If we managed to create any "x=x" assignments, remove them.
//      for (size_t j = 0; j < maybeRemoveNodes.size(); j++) {
//        Ref node = maybeRemoveNodes[j].second;
//        if (node[2][1] == node[3][1]) {
//          if (block->isexpr[maybeRemoveNodes[j].first]) {
//            safeCopy(node, node[2]);
//          } else {
//            safeCopy(node, makeEmpty());
//          }
//        }
//      }
//    }
//
//#ifdef PROFILING
//    tblockproc += clock() - start;
//    start = clock();
//#endif
//
//    // Assign registers to function params based on entry junction
//
//    StringSet paramRegs;
//    if (!!fun[2]) {
//      for (size_t i = 0; i < fun[2]->size(); i++) {
//        auto& allRegs = allRegsByType[asmData.getType(fun[2][i]->getIString())];
//        fun[2][i]->setString(allRegs[juncVars[nameToNum[fun[2][i]->getIString()]].reg]);
//        paramRegs.insert(fun[2][i]->getIString());
//      }
//    }
//
//    // That's it!
//    // Re-construct the function with appropriate variable definitions.
//
//    asmData.locals.clear();
//    asmData.params.clear();
//    asmData.vars.clear();
//    for (int i = 1; i < nextReg; i++) {
//      for (size_t type = 0; type < allRegsByType.size(); type++) {
//        if (allRegsByType[type].count(i) > 0) {
//          IString reg = allRegsByType[type][i];
//          if (!paramRegs.has(reg)) {
//            asmData.addVar(reg, intToAsmType(type));
//          } else {
//            asmData.addParam(reg, intToAsmType(type));
//          }
//          break;
//        }
//      }
//    }
//    asmData.denormalize();
//
//    removeAllUselessSubNodes(fun); // XXX vacuum?    vacuum(fun);
//
//#ifdef PROFILING
//    treconstruct += clock() - start;
//    start = clock();
//#endif
//
//  });
//#ifdef PROFILING
//  errv("    RH stages: a:%li fl:%li lf:%li bf:%li jvua:%li jvs:%li jra:%li bp:%li r:%li",
//    tasmdata, tflowgraph, tlabelfix, tbackflow, tjuncvaruniqassign, tjuncvarsort, tregassign, tblockproc, treconstruct);
//#endif
//}
//// end registerizeHarder

// minified names generation
lazy_static! {
    static ref RESERVED: phf::Set<IString> = iss![
        "do",
        "if",
        "in",
        "for",
        "new",
        "try",
        "var",
        "env",
        "let",
   ];
}
const VALID_MIN_INITS: &'static [u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";
const VALID_MIN_LATERS: &'static [u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$0123456789";

fn ensureMinifiedNames(n: usize, minifiedNames: &mut Vec<IString>, minifiedState: &mut Vec<usize>) { // make sure the nth index in minifiedNames exists. done 100% deterministically
    while minifiedNames.len() < n+1 {
        // generate the current name
        let mut name = [0u8; 3]; // RSNOTE: if this needs increasing, check RESERVED
        name[0] = VALID_MIN_INITS[minifiedState[0]];
        for i in 1..minifiedState.len() {
            name[i] = VALID_MIN_LATERS[minifiedState[i]]
        }
        let iname = IString::from(String::from_utf8(name[..minifiedState.len()].to_vec()).unwrap());
        if !RESERVED.contains(&iname) { minifiedNames.push(iname) }
        // increment the state
        let mut i = 0;
        minifiedState[i] += 1;
        loop {
            if minifiedState[i] < if i == 0 { VALID_MIN_INITS.len() } else { VALID_MIN_LATERS.len() } { break }
            // overflow
            minifiedState[i] = 0;
            i += 1;
            if i == minifiedState.len() {
                minifiedState.push(0)
            } else {
                minifiedState[i] += 1
            }
        }
    }
}

pub fn minifyLocals(ast: &mut AstValue, extraInfo: &serde_json::Value) {
    let globals: HashMap<&str, IString> = extraInfo.find("globals").unwrap().as_object().unwrap()
        .iter().map(|(key, val)| (key.as_str(), IString::from(val.as_str().unwrap()))).collect();

    // RSTODO: original code had these two as globals so they would be preserved across passes -
    // would they ever be used again? Maybe assert minifylocals is only called once?
    let mut minifiedNames = vec![];
    let mut minifiedState = vec![0];

    traverseFunctionsMut(ast, |fun: &mut AstValue| {

    // Analyse the asmjs to figure out local variable names,
    // but operate on the original source tree so that we don't
    // miss any global names in e.g. variable initializers.
    let asmDataLocals;
    {
    let mut asmData = AsmData::new(fun);
    asmData.denormalize(); // TODO: we can avoid modifying at all here - we just need a list of local vars+params
    asmDataLocals = asmData.locals
    }

    let mut newNames = HashMap::<IString, IString>::new();
    let mut usedNames = HashSet::<IString>::new();

    // Find all the globals that we need to minify using
    // pre-assigned names.  Don't actually minify them yet
    // as that might interfere with local variable names.
    traversePre(fun, |node: &AstValue| {
        if let Name(ref name) = *node {
            if !asmDataLocals.contains_key(name) {
                if let Some(minified) = globals.get(&**name) {
                    assert!(*minified != is!(""));
                    match newNames.entry(name.clone()) {
                        hash_map::Entry::Occupied(entry) => {
                            assert!(entry.get() == minified);
                            assert!(usedNames.contains(minified))
                        },
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert(minified.clone());
                            let isnew = usedNames.insert(minified.clone());
                            assert!(isnew);
                        },
                    };
                }
            }
        }
    });

    // The first time we encounter a local name, we assign it a
    // minified name that's not currently in use.  Allocating on
    // demand means they're processed in a predictable order,
    // which is very handy for testing/debugging purposes.
    let mut nextMinifiedName = 0;
    macro_rules! getNextMinifiedName {
        () => { getNextMinifiedNameAfter(&mut nextMinifiedName, &usedNames, &asmDataLocals, &mut minifiedNames, &mut minifiedState) }
    };
    fn getNextMinifiedNameAfter(nextMinifiedName: &mut usize, usedNames: &HashSet<IString>, asmDataLocals: &HashMap<IString, Local>, minifiedNames: &mut Vec<IString>, minifiedState: &mut Vec<usize>) -> IString {
        loop {
            ensureMinifiedNames(*nextMinifiedName, minifiedNames, minifiedState);
            let minified = &minifiedNames[*nextMinifiedName];
            *nextMinifiedName += 1;
            // TODO: we can probably remove !isLocalName here
            if !usedNames.contains(minified) && !asmDataLocals.contains_key(minified) {
                return minified.clone()
            }
        }
    }

    // We can also minify loop labels, using a separate namespace
    // to the variable declarations.
    let mut newLabels = HashMap::<IString, IString>::new();
    let mut nextMinifiedLabel = 0;
    macro_rules! getNextMinifiedLabel {
        () => { getNextMinifiedLabelAfter(&mut nextMinifiedLabel, &mut minifiedNames, &mut minifiedState) }
    };
    fn getNextMinifiedLabelAfter(nextMinifiedLabel: &mut usize, minifiedNames: &mut Vec<IString>, minifiedState: &mut Vec<usize>) -> IString {
         ensureMinifiedNames(*nextMinifiedLabel, minifiedNames, minifiedState);
         let ret = minifiedNames[*nextMinifiedLabel].clone();
         *nextMinifiedLabel += 1;
         ret
    }

    // Traverse and minify all names.
    let (fname, args, stats) = fun.getMutDefun();
    if let Some(newfname) = globals.get(&**fname) {
        *fname = newfname.clone()
    }
    for arg in args.iter_mut() {
        let minified = getNextMinifiedName!();
        let prev = newNames.insert(mem::replace(arg, minified.clone()), minified);
        assert!(prev.is_none());
    }
    for stat in stats.iter_mut() {
        traversePreMut(stat, |node: &mut AstValue| {
            match *node {
                Name(ref mut name) => {
                    if let Some(minified) = newNames.get(name) {
                        assert!(*minified != is!(""));
                        *name = minified.clone();
                        return
                    }
                    // RSTODO: this would just be else-if without the early return, but lexical borrows...
                    if asmDataLocals.contains_key(name) {
                        let minified = getNextMinifiedName!();
                        let prev = newNames.insert(mem::replace(name, minified.clone()), minified);
                        assert!(prev.is_none());
                    }
                },
                Var(ref mut vars) => {
                    for &mut (ref mut name, _) in vars.iter_mut() {
                        if let Some(minified) = newNames.get(name) {
                            *name = minified.clone();
                            return
                        }
                        // RSTODO: again, lexical borrows (note early return)
                        // else {
                            let minified = getNextMinifiedName!();
                            let prev = newNames.insert(mem::replace(name, minified.clone()), minified);
                            assert!(prev.is_none());
                        //}
                    }
                },
                Label(ref mut label, _) => {
                    if let Some(minified) = newLabels.get(label) {
                        *label = minified.clone();
                        return
                    }
                    // RSTODO: again, lexical borrows (note early return)
                    // else {
                        let minified = getNextMinifiedLabel!();
                        let prev = newLabels.insert(mem::replace(label, minified.clone()), minified);
                        assert!(prev.is_none());
                    //}
                },
                Break(Some(ref mut maybelabel)) |
                Continue(Some(ref mut maybelabel)) => {
                    *maybelabel = newLabels.get(maybelabel).unwrap().clone()
                },
                _ => (),
            }
        })
    }

    })
}

// RSTODO
//void asmLastOpts(Ref ast) {
//  std::vector<Ref> statsStack;
//  traverseFunctions(ast, [&](Ref fun) {
//    traversePrePost(fun, [&](Ref node) {
//      Ref type = node[0];
//      Ref stats = getStatements(node);
//      if (!!stats) statsStack.push_back(stats);
//      if (CONDITION_CHECKERS.has(type)) {
//        node[1] = simplifyCondition(node[1]);
//      }
//      if (type == WHILE && node[1][0] == NUM && node[1][1]->getNumber() == 1 && node[2][0] == BLOCK && node[2]->size() == 2) {
//        // This is at the end of the pipeline, we can assume all other optimizations are done, and we modify loops
//        // into shapes that might confuse other passes
//
//        // while (1) { .. if (..) { break } } ==> do { .. } while(..)
//        Ref stats = node[2][1];
//        Ref last = stats->back();
//        if (!!last && last[0] == IF && (last->size() < 4 || !last[3]) && last[2][0] == BLOCK && !!last[2][1][0]) {
//          Ref lastStats = last[2][1];
//          int lastNum = lastStats->size();
//          Ref lastLast = lastStats[lastNum-1];
//          if (!(lastLast[0] == BREAK && !lastLast[1])) return;// if not a simple break, dangerous
//          for (int i = 0; i < lastNum; i++) {
//            if (lastStats[i][0] != STAT && lastStats[i][0] != BREAK) return; // something dangerous
//          }
//          // ok, a bunch of statements ending in a break
//          bool abort = false;
//          int stack = 0;
//          int breaks = 0;
//          traversePrePost(stats, [&](Ref node) {
//            Ref type = node[0];
//            if (type == CONTINUE) {
//              if (stack == 0 || !!node[1]) { // abort if labeled (we do not analyze labels here yet), or a continue directly on us
//                abort = true;
//              }
//            } else if (type == BREAK) {
//              if (stack == 0 || !!node[1]) { // relevant if labeled (we do not analyze labels here yet), or a break directly on us
//                breaks++;
//              }
//            } else if (LOOP.has(type)) {
//              stack++;
//            }
//          }, [&](Ref node) {
//            if (LOOP.has(node[0])) {
//              stack--;
//            }
//          });
//          if (abort) return;
//          assert(breaks > 0);
//          if (lastStats->size() > 1 && breaks != 1) return; // if we have code aside from the break, we can only move it out if there is just one break
//          if (statsStack.size() < 1) return; // no chance we have this stats on hand
//          // start to optimize
//          if (lastStats->size() > 1) {
//            Ref parent = statsStack.back();
//            int me = parent->indexOf(node);
//            if (me < 0) return; // not always directly on a stats, could be in a label for example
//            parent->insert(me+1, lastStats->size()-1);
//            for (size_t i = 0; i+1 < lastStats->size(); i++) {
//              parent[me+1+i] = lastStats[i];
//            }
//          }
//          Ref conditionToBreak = last[1];
//          stats->pop_back();
//          node[0]->setString(DO);
//          node[1] = simplifyNotCompsDirect(make2(UNARY_PREFIX, L_NOT, conditionToBreak));
//        }
//      } else if (type == BINARY) {
//        if (node[1] == AND) {
//          if (node[3][0] == UNARY_PREFIX && node[3][1] == MINUS && node[3][2][0] == NUM && node[3][2][1]->getNumber() == 1) {
//            // Change &-1 into |0, at this point the hint is no longer needed
//            node[1]->setString(OR);
//            node[3] = node[3][2];
//            node[3][1]->setNumber(0);
//          }
//        } else if (node[1] == MINUS && node[3][0] == UNARY_PREFIX) {
//          // avoid X - (-Y) because some minifiers buggily emit X--Y which is invalid as -- can be a unary. Transform to
//          //        X + Y
//          if (node[3][1] == MINUS) { // integer
//            node[1]->setString(PLUS);
//            node[3] = node[3][2];
//          } else if (node[3][1] == PLUS) { // float
//            if (node[3][2][0] == UNARY_PREFIX && node[3][2][1] == MINUS) {
//              node[1]->setString(PLUS);
//              node[3][2] = node[3][2][2];
//            }
//          }
//        }
//      }
//    }, [&](Ref node) {
//      if (statsStack.size() > 0) {
//        Ref stats = getStatements(node);
//        if (!!stats) statsStack.pop_back();
//      }
//    });
//    // convert  { singleton }  into  singleton
//    traversePre(fun, [](Ref node) {
//      if (node[0] == BLOCK && !!getStatements(node) && node[1]->size() == 1) {
//        safeCopy(node, node[1][0]);
//      }
//    });
//    // convert L: do { .. } while(0) into L: { .. }
//    traversePre(fun, [](Ref node) {
//      if (node[0] == LABEL && node[1]->isString() /* careful of var label = 5 */ &&
//          node[2][0] == DO && node[2][1][0] == NUM && node[2][1][1]->getNumber() == 0 && node[2][2][0] == BLOCK) {
//        // there shouldn't be any continues on this, not direct break or continue
//        IString label = node[1]->getIString();
//        bool abort = false;
//        int breakCaptured = 0, continueCaptured = 0;
//        traversePrePost(node[2][2], [&](Ref node) {
//          if (node[0] == CONTINUE) {
//            if (!node[1] && !continueCaptured) {
//              abort = true;
//            } else if (node[1]->isString() && node[1]->getIString() == label) {
//              abort = true;
//            }
//          }
//          if (node[0] == BREAK && !node[1] && !breakCaptured) {
//            abort = true;
//          }
//          if (BREAK_CAPTURERS.has(node[0])) {
//            breakCaptured++;
//          }
//          if (CONTINUE_CAPTURERS.has(node[0])) {
//            continueCaptured++;
//          }
//        }, [&](Ref node) {
//          if (BREAK_CAPTURERS.has(node[0])) {
//            breakCaptured--;
//          }
//          if (CONTINUE_CAPTURERS.has(node[0])) {
//            continueCaptured--;
//          }
//        });
//        if (abort) return;
//        safeCopy(node[2], node[2][2]);
//      }
//    });
//  });
//}

// Contrary to the name this does not eliminate actual dead functions, only
// those marked as such with DEAD_FUNCTIONS
pub fn eliminateDeadFuncs(ast: &mut AstValue, extraInfo: &serde_json::Value) {
    let mut deadfns = HashSet::new();
    for deadfn in extraInfo.find("dead_functions").unwrap().as_array().unwrap() {
        let isnew = deadfns.insert(deadfn.as_str().unwrap());
        assert!(isnew);
    }

    traverseFunctionsMut(ast, |fun: &mut AstValue| {

    if !deadfns.contains(&**fun.getDefun().0) { return }
    let mut asmData = AsmData::new(fun);
    {
    let (_, _, stats) = asmData.func.getMutDefun();
    *stats = makeArray(1);
    let mut params = makeArray(1);
    params.push(makeNum(-1f64));
    stats.push(an!(Stat(an!(Call(makeName(is!("abort")), params)))));
    }
    asmData.vars.clear();
    asmData.denormalize();

    })
}
