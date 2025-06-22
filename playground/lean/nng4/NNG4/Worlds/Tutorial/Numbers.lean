import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.OneEqSuccZero
import NNG4.Theorems.TwoEqSuccOne

example : (2 : ℕ) = .succ (.succ 0) := by
  rw[two_eq_succ_one]
  rw[one_eq_succ_zero]
  rfl
