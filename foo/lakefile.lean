import Lake
open Lake DSL

package «HigherRankedSyntax» where
  -- add package configuration options here
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «HigherRankedSyntax» where
  -- add library configuration options here
