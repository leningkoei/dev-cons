import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulZero
import NNG4.Theorems.ZeroMul
import NNG4.Theorems.MulSucc
import NNG4.Theorems.SuccMul

theorem mul_comm (a b : ℕ)
: a * b = b * a
:= by
  induction b with d hd
  rw[mul_zero a]
  rw[zero_mul a]
  rfl
  rw[mul_succ a d]
  rw[succ_mul d a]
  rw[hd]
  rfl
