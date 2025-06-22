namespace Note

#check @IO.println

inductive Pos where
| Pos.one : Pos
| Pos.succ : Pos → Pos

def Pos.add : Pos → Pos → Pos
| Pos.one, y => Pos.succ y
| Pos.succ x, y => Pos.succ (x.add y)

instance : Add Pos where
  add := Pos.add

def List.sum [Add α] [OfNat α 0] : List α → α
| [] => 0
| x :: xs => x + xs.sum

#check OfNat.ofNat

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Add α] : Add (PPoint α) where
  add p1 p2 := {
    x := p1.x + p2.x
    y := p1.y + p2.y
  }

end Note

namespace Exercise

/- Even Number Literals
Write an instance of `OfNat` for the even number datatype from the
*previsous section's exercises* that uses recursive instance search. For the
base instance, it is necessary to write `OfNat Even Nat.zero` instead of
`OfNat Even 0`.
-/

inductive Even : Type where
| zero : Even
| succ2 : Even → Even

def Even.add : Even → Even → Even
| Even.zero, y => y
| Even.succ2 x, y => Even.succ2 <| x.add y

def Even.two := Even.succ2 Even.zero
def Even.four := Even.succ2 Even.two

#eval Even.two.add Even.four

instance : Add Even where
  add := Even.add

#eval Even.two + Even.four

def Even.mul : Even → Even → Even
| Even.zero, _ => Even.zero
| Even.succ2 x, y => x.mul y + y + y

instance : Mul Even where
  mul := Even.mul

#eval Even.two * Even.four

def Even.toNat : Even → Nat
| Even.zero => 0
| Even.succ2 x => x.toNat + 2

instance : ToString Even where
  toString := ToString.toString ∘ Even.toNat

#eval Even.two * Even.four

instance : OfNat Even 0 where
  ofNat := Even.zero
instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.succ2 (OfNat.ofNat n)

#eval (2 : Even)

/- Recursive Instance Search Depth
There is a limit to how many times the Lean compiler will attempt a recursive
instance search. This places a limit on the size of even number literals defined
in the previous exercise. Experimentally determine what the limit is.
-/

end Exercise
