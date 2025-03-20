import Lake
open Lake DSL

package «fos» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Fos» {
  -- add library configuration options here
}

require "leanprover-community" / "mathlib"
