import Lake

open Lake DSL

package «qed» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- The QED formalization library. Every module under `QED/` is built by
`lake build`, so no module can escape compilation by being unreachable from
the root `QED.lean`. -/
@[default_target]
lean_lib «QED» where
  globs := #[.andSubmodules `QED]
  leanOptions := projectLeanOptions
