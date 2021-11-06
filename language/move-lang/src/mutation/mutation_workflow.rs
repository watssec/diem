use crate::{parser::ast::{BinOp_, BinOp}};
use move_ir_types::location::sp;


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

