import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulComm
import NNG4.Theorems.MulAdd

theorem add_mul (a b c : ℕ)
: (a + b) * c = a * c + b * c
:= by
  rw[mul_comm (a + b) c]
  rw[mul_comm a c]
  rw[mul_comm b c]
  rw[mul_add c a b]
  rfl
