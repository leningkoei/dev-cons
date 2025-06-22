import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc

theorem succ_add (a b : ℕ)
: .succ a + b = .succ (a + b)
:= by
  induction b with d hd
  rw[add_zero (.succ a)]
  rw[add_zero a]
  rfl
  rw[add_succ (.succ a) d]
  rw[add_succ a d]
  rw[hd]
  rfl
