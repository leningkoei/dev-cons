import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.OneEqSuccZero


theorem succ_eq_add_one (n : ℕ)
: .succ n = n + 1
:= by
  rw[one_eq_succ_zero]
  rw[add_succ n 0]
  rw[add_zero n]
  rfl
