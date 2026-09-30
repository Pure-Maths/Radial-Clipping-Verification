import Lake
open Lake DSL

package H099Formalization where
  moreLeanArgs := #["-DmaxHeartbeats=2000000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

@[default_target]
lean_lib H099
