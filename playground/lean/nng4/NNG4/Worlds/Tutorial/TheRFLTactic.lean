import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL

example (x q : ℕ)
: 37 * x + q = 37 * x + q
:= by
  rfl
