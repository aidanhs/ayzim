#![feature(plugin_registrar, rustc_private)]

extern crate syntax;
extern crate rustc;
extern crate rustc_plugin;

use syntax::codemap::Span;
use syntax::tokenstream::TokenTree;
use syntax::ext::base::{ExtCtxt, MacResult, MacEager};
use syntax::ext::build::AstBuilder;  // trait for expr_usize
use rustc_plugin::Registry;

use syntax::ast::{Pat, PatKind};
use syntax::ptr::P;

// Stolen from libsyntax/ast.rs
// Changed fn args and name
// s/self/pat/g
// Cond at beginning became `let mut pat = it(pat);`
// s/ref /ref mut /g
// s/iter(/iter_mut(/g
// s/true/()/g
// s/ &&$/;/g
// s/\.all(\(.*\);$/\.map(\1.count();/g
// s/ \([a-z]\)\.walk(it)/ *\1 = \1.map(|p| walk_pat_mut(p, it))/g
// rest by hand
pub fn walk_pat_mut<F>(pat: Pat, it: &mut F) -> Pat where F: FnMut(Pat) -> Pat {
    let mut pat = it(pat);

    match pat.node {
        PatKind::Ident(_, _, Some(ref mut p)) => {
            *p = p.clone().map(|p| walk_pat_mut(p, it));
        },
        PatKind::Struct(_, ref mut fields, _) => {
            fields.iter_mut().map(|field| field.node.pat = field.node.pat.clone().map(|p| walk_pat_mut(p, it))).count();
        }
        PatKind::TupleStruct(_, ref mut s, _) | PatKind::Tuple(ref mut s, _) => {
            s.iter_mut().map(|p| *p = p.clone().map(|p| walk_pat_mut(p, it))).count();
        }
        PatKind::Box(ref mut s) | PatKind::Ref(ref mut s, _) => {
            *s = s.clone().map(|p| walk_pat_mut(p, it));
        }
        PatKind::Slice(ref mut before, ref mut slice, ref mut after) => {
            before.iter_mut().map(|p| *p = p.clone().map(|p| walk_pat_mut(p, it))).count();
            slice.iter_mut().map(|p| *p = p.clone().map(|p| walk_pat_mut(p, it))).count();
            after.iter_mut().map(|p| *p = p.clone().map(|p| walk_pat_mut(p, it))).count();
        }
        PatKind::Wild |
        PatKind::Lit(_) |
        PatKind::Range(_, _) |
        PatKind::Ident(_, _, _) |
        PatKind::Path(..) |
        PatKind::Mac(_) => {
            ()
        }
    };
    pat
}

fn expand_mast(cx: &mut ExtCtxt, sp: Span, args: &[TokenTree]) -> Box<MacResult + 'static> {
    let mut parser = cx.new_parser_from_tts(args);
    let pat = parser.parse_pat().unwrap().unwrap();
    let mut skip = true;
    let pat = walk_pat_mut(pat, &mut |pat| {
        // Blindly add `box ` to the beginning of any tuple struct
        if let PatKind::TupleStruct(_, _, _) = pat.node {
            skip = !skip;
            if skip { pat } else { cx.pat(sp, PatKind::Box(P(pat))).unwrap() }
        } else {
            pat
        }
    });
    MacEager::pat(cx.pat(sp, pat.node.clone()))
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("mast", expand_mast);
}
