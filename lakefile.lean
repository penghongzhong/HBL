import Lake
open Lake DSL
package hbl
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "a98628e16c11f5167f16124105ddce53efa9bfe5"
@[default_target]
lean_lib HBL
