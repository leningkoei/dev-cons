import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulOne
import NNG4.Theorems.MulComm

theorem one_mul (m : ℕ)
: 1 * m = m
:= by
  rw[mul_comm 1 m]
  rw[mul_one m]
  rfl
