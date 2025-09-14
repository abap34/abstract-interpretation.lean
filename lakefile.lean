import Lake
open Lake DSL

package "galois-connection" where
  version := v!"0.1.0"

require mathlib from git
    "https://github.com/leanprover-community/mathlib4.git" @"master"

@[default_target]
lean_lib «GaloisConnection» where
  -- add library configuration options here
