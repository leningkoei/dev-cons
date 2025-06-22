namespace Note

inductive Pos where
| one : Pos
| succ : Pos → Pos

instance : OfNat Pos 1 where
  ofNat := Pos.one
instance [OfNat Pos n] : OfNat Pos (n + 1) where
  ofNat := Pos.succ (OfNat.ofNat n)

def addNatPos : Nat → Pos → Pos
| 0, p => p
| n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos := flip addNatPos

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos
-- instance : HPlus Pos Nat Nat where
--   hPlus := λ _ => λ _ => 6
instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#check HAdd.hAdd
#check HPlus.hPlus
-- def b := HAdd.hAdd (3 : Pos) (4 : Nat)
#eval (HPlus.hPlus (3 : Pos) (4 : Nat) :)

end Note

namespace Exercise

/-
Define an instance of `HMul (PPoint α) α (PPoint α)` that multiplies both
projections by the scalar. It should work for any type α for which there is a
`Mul α` instance. For example,
> #eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
should yield
> { x := 5.00000, y:= 7.400000 }
-/

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p k := {
    x := p.x * k
    y := p.y * k
  }

#eval { x := 2.5, y:= 3.7 : PPoint Float } * 2.0

end Exercise
