import Lake
open Lake DSL

package «lean4-example» {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

@[default_target]
lean_lib «Lean4Example» {
}
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.2.0"
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
