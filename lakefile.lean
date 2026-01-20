import Lake
open Lake DSL

package "abstract-interpretation" where
  version := v!"0.1.0"

require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @"master"

@[default_target]
lean_lib «AbstractInterpretation» where
  -- add library configuration options here
