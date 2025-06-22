import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc

theorem add_assoc (a b c : ℕ)
: a + b + c = a + (b + c)
:= by
  induction c with d hd
  rw[add_zero (a + b)]
  rw[add_zero b]
  rfl
  rw[add_succ (a + b)]
  rw[add_succ b d]
  rw[add_succ a (b + d)]
  rw[hd]
  rfl
