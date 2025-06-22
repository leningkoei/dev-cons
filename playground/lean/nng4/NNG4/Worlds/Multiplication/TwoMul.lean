import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccAdd
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc
import NNG4.Theorems.TwoEqSuccOne

theorem two_mul (m : ℕ)
: 2 * m = m + m
:= by
  induction m with d hd
  rw[mul_zero 2]
  rw[add_zero 0]
  rfl
  rw[mul_succ 2 d]
  rw[add_succ (.succ d) d]
  rw[succ_add d d]
  rw[succ_eq_add_one (.succ (d + d))]
  rw[succ_eq_add_one (d + d)]
  rw[add_assoc (d + d) 1 1]
  rw[← succ_eq_add_one 1]
  rw[← two_eq_succ_one]
  rw[hd]
  rfl
