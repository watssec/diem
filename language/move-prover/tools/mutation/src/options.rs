// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use structopt::StructOpt;


/// Options passed into the specification flattening tool.
#[derive(StructOpt, Clone,Debug)]
pub struct MutationOptions {

    /// Sources of the target modules
    pub srcs: Vec<String>,

    /// Dependencies
    #[structopt(short = "d", long = "dependency")]
    pub deps: Vec<String>,

    /// Do not include default named address
    #[structopt(long = "no-default-named-addresses")]
    pub no_default_named_addresses: bool,

    /// Target function
    #[structopt(short, long)]
    pub target: Option<String>,

}
