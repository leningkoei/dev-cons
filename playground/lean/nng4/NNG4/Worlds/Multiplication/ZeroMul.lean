import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc

theorem zero_mul (m : ℕ)
: 0 * m = 0
:= by
  induction m with d hd
  rw[mul_zero 0]
  rfl
  rw[mul_succ 0 d]
  rw[add_zero (0 * d)]
  rw[hd]
  rfl
