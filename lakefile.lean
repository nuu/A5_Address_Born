import Lake
open Lake DSL

package «A5Paper3» where

-- Reproducibility note:
-- `@ "master"` tracks a moving target and will eventually drift past the pinned
-- Lean toolchain (lean-toolchain: leanprover/lean4:v4.29.0-rc6). For an archival
-- build, replace "master" with the exact Mathlib commit/tag that compiles under
-- this toolchain, and commit the resulting `lake-manifest.json` to the deposit.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «A5Born» where
