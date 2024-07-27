import Lake
open Lake DSL

package «chapter1» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require aesop from git "https://github.com/JLimperg/aesop"

@[default_target]
lean_lib «Chapter1» where
  -- add any library configuration options here
