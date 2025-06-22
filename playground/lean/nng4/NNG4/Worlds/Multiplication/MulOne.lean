import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.ZeroAdd
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc
import NNG4.Theorems.OneEqSuccZero

theorem mul_one (m : ℕ)
: m * 1 = m
:= by
  rw[one_eq_succ_zero]
  rw[mul_succ m 0]
  rw[mul_zero m]
  rw[zero_add m]
  rfl
