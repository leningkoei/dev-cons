import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.AddRightComm
import NNG4.Theorems.ZeroMul
import NNG4.Theorems.SuccMul
import NNG4.Theorems.MulComm

theorem mul_add (a b c : ℕ)
: a * (b + c) = a * b + a * c
:= by
  induction a with d hd
  rw[zero_mul (b + c)]
  rw[zero_mul b]
  rw[zero_mul c]
  rw[add_zero 0]
  rfl
  rw[succ_mul d (b + c)]
  rw[succ_mul d b]
  rw[succ_mul d c]
  rw[← add_assoc (d * b + b) (d * c) c]
  rw[add_right_comm (d * b) b (d * c)]
  rw[add_assoc (d * b + d * c) b c]
  rw[hd]
  rfl
