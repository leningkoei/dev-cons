import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.ZeroAdd
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccAdd

theorem add_comm (a b : ℕ)
: a + b = b + a
:= by
  induction b with d hd
  rw[add_zero a]
  rw[zero_add a]
  rfl
  rw[add_succ a d]
  rw[succ_add d a]
  rw[hd]
  rfl
