import Lake
open Lake DSL

package «Gametheory» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Gametheory» {
  -- add library configuration options here
}

@[default_target]
lean_lib «BeyondSperner» {
  -- Ivanov's “Beyond Sperner's Lemma” formalization lives in its own module tree.
}

@[default_target]
lean_lib «FormalizationInterface» {
  -- Compatibility adapters, status documentation, and axiom audits stay outside the math tree.
}

--require llmlean from git
--  "https://github.com/jiajunma/llmlean.git"@"main"-/

--require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"@"main"

require "leanprover-community" / "mathlib" @ git "v4.33.0"
