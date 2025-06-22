import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc

theorem succ_mul (a b : ℕ)
: .succ a * b = a * b + b
:= by
  induction b with d hd
  rw[mul_zero (.succ a)]
  rw[mul_zero a]
  rw[add_zero 0]
  rfl
  rw[mul_succ (.succ a) d]
  rw[mul_succ a d]
  rw[add_assoc (a * d) a (.succ d)]
  rw[add_succ a d]
  rw[add_comm a d]
  rw[← add_succ d a]
  rw[← add_assoc (a * d) d (.succ a)]
  rw[hd]
  rfl
