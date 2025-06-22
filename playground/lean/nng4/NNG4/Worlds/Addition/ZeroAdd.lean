import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc

theorem zero_add (n : ℕ)
: 0 + n = n
:= by
  induction n with d hd
  rw[add_zero 0]
  rfl
  rw[add_succ 0 d]
  rw[hd]
  rfl
