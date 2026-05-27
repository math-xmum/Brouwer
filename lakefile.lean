import Lake
open Lake DSL

package «Gametheory» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Gametheory» {
  -- add library configuration options here
}

--require llmlean from git
--  "https://github.com/jiajunma/llmlean.git"@"main"-/

--require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"@"main"

require "leanprover-community" / "mathlib" @ git "v4.30.0"
