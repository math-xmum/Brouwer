import Lake
open Lake DSL

package «Gametheory» {
  packageDir := "../.lake/packages"
}

@[default_target]
lean_lib «Gametheory» {
  -- add library configuration options here
}

--require llmlean from git
--  "https://github.com/jiajunma/llmlean.git"@"main"-/

--require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"@"main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
