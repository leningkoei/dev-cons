import Lake
open Lake DSL

package nng4 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"

@[default_target]
lean_lib NNG4 where

lean_exe nng4 where
  root := `Main
  supportInterpreter := .true
