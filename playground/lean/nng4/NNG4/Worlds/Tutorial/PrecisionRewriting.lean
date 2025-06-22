import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.AddZero

example (a b c : ℕ)
: a + (b + 0) + (c + 0) = a + b + c
:= by
  repeat rw[add_zero]
  rfl
