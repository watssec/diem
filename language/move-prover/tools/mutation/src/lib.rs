// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
mod options;
mod workflow;

pub use options::MutationOptions;

//**************************************************************************************************
// Entrypoint
//**************************************************************************************************

pub fn run(options: &MutationOptions) -> Result<()> {

    // return env and target from
    let (env, targets) = workflow::prepare(options)?;

    // make sure the original verification works
    let proved = workflow::prove(options, &env, &targets)?;
    if !proved {
        return Err(anyhow!("Original proof is not successful"));
    }

    // everything is OK
    Ok(())
}
