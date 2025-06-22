import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW

example (x y : ℕ) (h : y = x + 7)
: 2 * y = 2 * (x + 7)
:= by
  rw[h]
  rfl
