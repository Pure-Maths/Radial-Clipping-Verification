import Lake
open Lake DSL

package SharpRadialClippingFormalization where
  moreLeanArgs := #["-DmaxHeartbeats=2000000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

@[default_target]
lean_lib SharpRadialClipping
