inductive Pos where
| one : Pos
| succ : Pos → Pos

def Pos.toNat : Pos → Nat
| Pos.one => 1
| Pos.succ n => n.toNat + 1

instance : OfNat Pos (n + 1) where
  ofNat := natPlusOne n where
    natPlusOne : Nat → Pos
    | 0 => Pos.one
    | n + 1 => Pos.succ (natPlusOne n)

#eval (8 : Pos).toNat

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)
