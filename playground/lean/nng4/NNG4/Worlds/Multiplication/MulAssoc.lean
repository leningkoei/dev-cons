import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc
import NNG4.Theorems.MulAdd

theorem mul_assoc (a b c : ℕ)
: (a * b) * c = a * (b * c)
:= by
  induction c with d hd
  rw[mul_zero (a * b)]
  rw[mul_zero b]
  rw[mul_zero a]
  rfl
  rw[mul_succ (a * b) d]
  rw[mul_succ b d]
  rw[mul_add a (b * d) b]
  rw[hd]
  rfl
