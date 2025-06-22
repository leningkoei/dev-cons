import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddAssoc

theorem add_right_comm (a b c : ℕ)
: a + b + c = a + c + b
:= by
  rw[add_assoc a b c]
  rw[add_assoc a c b]
  rw[add_comm b c]
  rfl
