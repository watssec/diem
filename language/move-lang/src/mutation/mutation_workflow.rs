use crate::{typing::{ast as T, core::Context}, naming::ast::Exp_, parser::ast::{BinOp_, BinOp}, shared::{unique_map::UniqueMap, *}, expansion::ast::{Fields, ModuleIdent, Value_}};
use move_ir_types::location::sp;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use move_symbol_pool::Symbol;

// Expression Mutation

pub fn expression_mutation(op: BinOp ) ->BinOp {

    match op.value {
        BinOp_::Add => {
            sp(op.loc, BinOp_::Sub)
        }
        BinOp_::Sub => {
            sp(op.loc, BinOp_::Add)
        }
        BinOp_::Mul => {
            sp(op.loc, BinOp_::Div)
        }
        BinOp_::Div => {
            sp(op.loc, BinOp_::Mul)
        }

        _ => op
    }

}

