import Lake
open Lake DSL

package fpl where

lean_lib Fpl where

lean_exe fpl where
  root := `Main
  supportInterpreter := true
