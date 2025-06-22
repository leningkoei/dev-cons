import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.OneEqSuccZero
import NNG4.Theorems.TwoEqSuccOne
import NNG4.Theorems.ThreeEqSuccTwo
import NNG4.Theorems.FourEqSuccThree

example
: (2 : ℕ) + 2 = 4
:= by
  rw[two_eq_succ_one]
  rw[add_succ (.succ 1) 1]
  rw[← succ_eq_add_one (.succ 1)]
  rw[← two_eq_succ_one]
  rw[← three_eq_succ_two]
  rw[← four_eq_succ_three]
  rfl
