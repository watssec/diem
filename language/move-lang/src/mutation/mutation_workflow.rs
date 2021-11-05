use crate::{typing::{ast as T, core::Context}, naming::ast::Exp_, parser::ast::BinOp_, shared::{unique_map::UniqueMap, *}, expansion::ast::{Fields, ModuleIdent, Value_}};
use move_ir_types::location::sp;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use move_symbol_pool::Symbol;
pub fn mutation_workflow(original: Exp_) ->Exp_ {
    match original.clone() {
        Exp_::BinopExp(lhs, op, rhs) => {
            match op.value {
                BinOp_::Add => {
                    Exp_::BinopExp(lhs, sp(op.loc, BinOp_::Sub),rhs)
                }
                _ => original
            }
        }
        _ => original
    }

}

