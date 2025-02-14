// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

pub mod compilation;
pub mod resolution;
pub mod source_package;

use anyhow::Result;
use compilation::compiled_package::CompilationCachingStatus;
use move_model::model::GlobalEnv;
use serde::{Deserialize, Serialize};
use source_package::layout::SourcePackageLayout;
use std::{
    io::Write,
    path::{Path, PathBuf},
};
use structopt::*;

use crate::{
    compilation::{
        build_plan::BuildPlan, compiled_package::CompiledPackage, model_builder::ModelBuilder,
    },
    resolution::resolution_graph::{ResolutionGraph, ResolvedGraph},
    source_package::{layout, manifest_parser},
};

#[derive(Debug, StructOpt, Clone, Serialize, Deserialize, Eq, PartialEq, PartialOrd)]
#[structopt(
    name = "Move Package",
    about = "Package and build system for Move code."
)]
pub struct BuildConfig {
    /// Compile in 'dev' mode. The 'dev-addresses' and 'dev-dependencies' fields will be used if
    /// this flag is set. This flag is useful for development of packages that expose named
    /// addresses that are not set to a specific value.
    #[structopt(name = "dev-mode", short = "d", long = "dev")]
    pub dev_mode: bool,

    /// Compile in 'test' mode. The 'dev-addresses' and 'dev-dependencies' fields will be used
    /// along with any code in the 'test' directory.
    #[structopt(name = "test-mode", short = "t", long = "test")]
    pub test_mode: bool,

    /// Generate documentation for packages
    #[structopt(name = "generate-docs", long = "doc")]
    pub generate_docs: bool,

    /// Generate ABIs for packages
    #[structopt(name = "generate-abis", long = "abi")]
    pub generate_abis: bool,

    /// Optional installation directory for this after it has been generated.
    #[structopt(long = "install-dir", parse(from_os_str))]
    pub install_dir: Option<PathBuf>,

    /// Force recompilation of all packages
    #[structopt(name = "force-recompilation", long = "force", short = "f")]
    pub force_recompilation: bool,
}

impl Default for BuildConfig {
    fn default() -> Self {
        Self {
            dev_mode: false,
            test_mode: false,
            generate_docs: false,
            generate_abis: false,
            install_dir: None,
            force_recompilation: false,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd)]
pub struct ModelConfig {
    pub all_files_as_targets: bool,
}

impl BuildConfig {
    /// Compile the package at `path` or the containing Move package.
    pub fn compile_package<W: Write>(self, path: &Path, writer: &mut W) -> Result<CompiledPackage> {
        Ok(self.compile_package_with_caching_info(path, writer)?.0)
    }

    /// Compile the package at `path` or the containing Move package and return whether or not all
    /// packages and dependencies were cached or not.
    pub fn compile_package_with_caching_info<W: Write>(
        self,
        path: &Path,
        writer: &mut W,
    ) -> Result<(CompiledPackage, CompilationCachingStatus)> {
        let resolved_graph = self.resolution_graph_for_package(path)?;
        BuildPlan::create(resolved_graph)?.compile(writer)
    }

    // NOTE: If there are now renamings, then the root package has the global resolution of all named
    // addresses in the package graph in scope. So we can simply grab all of the source files
    // across all packages and build the Move model from that.
    // TODO: In the future we will need a better way to do this to support renaming in packages
    // where we want to support building a Move model.
    pub fn move_model_for_package(
        self,
        path: &Path,
        model_config: ModelConfig,
    ) -> Result<GlobalEnv> {
        let resolved_graph = self.resolution_graph_for_package(path)?;
        ModelBuilder::create(resolved_graph, model_config).build_model()
    }

    pub fn resolution_graph_for_package(mut self, path: &Path) -> Result<ResolvedGraph> {
        if self.test_mode {
            self.dev_mode = true;
        }
        let path = SourcePackageLayout::try_find_root(path)?;
        let manifest_string =
            std::fs::read_to_string(path.join(layout::SourcePackageLayout::Manifest.path()))?;
        let toml_manifest = manifest_parser::parse_move_manifest_string(manifest_string)?;
        let manifest = manifest_parser::parse_source_manifest(toml_manifest)?;
        let resolution_graph = ResolutionGraph::new(manifest, path, self)?;
        resolution_graph.resolve()
    }
}
