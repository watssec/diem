// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::collections::BTreeMap;
use std::fs::OpenOptions;
mod options;
mod workflow;
use std::io::prelude::*;
pub use options::MutationOptions;
use std::path::Path;
//**************************************************************************************************
// Entrypoint
//**************************************************************************************************

pub fn run(options: &MutationOptions) -> Result<()> {


    let mut init_flag = true;
    // return env and target from
    let (env, targets) = workflow::prepare(options, &init_flag)?;
    let mut result_map = BTreeMap::new();
    // if the report file does not exist, create the file
    let mut file = if Path::new("../mutation_result.txt").exists(){
        OpenOptions::new().append(true).open("../mutation_result.txt")?
    }else{
        OpenOptions::new().write(true).create(true).open("../mutation_result.txt")?
    };

    init_flag = false;
    // iterate through the iterator
    for (loc, result) in env.mutation_result{
        let (env,targets) = workflow::prepare(options, &init_flag)?;
        let proved = workflow::prove(options, &env, &targets)?;
        if !proved{
            result_map.insert(loc, true);
        }else{
            result_map.insert(loc, false);
            write!(&mut file,"loc{:?}, arithmatic expression mutation",loc)?;
        }
    }


    // everything is OK
    Ok(())
}


