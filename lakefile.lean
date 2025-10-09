import Lake
open Lake DSL

package rnt_formal_proof where
  name := "rnt_formal_proof"
  leanLibConfigs := #[{
    name := "RNTProof",
    default := true
  }]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"
