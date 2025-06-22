inductive Vect (α : Type u) : Nat → Type u where
| nil : Vect α 0
| cons : α → Vect α n → Vect α (n + 1)

#print Vect

#eval Vect.cons 1 .nil

private theorem hAdd_zero (n : Nat) : n = 0 + n := by simp_arith
private theorem hAdd_succ (n₁ : Nat) (n₂ : Nat)
: (n₁ + n₂ + 1) = (n₁ + 1 + n₂) := by simp_arith

def Vect.append
: Vect α n₁ → Vect α n₂ → Vect α (n₁ + n₂)
| .nil, v₂ => hAdd_zero n₂ ▸ v₂
| .cons x₁ v₁', v₂ => hAdd_succ _ n₂ ▸ .cons x₁ (Vect.append v₁' v₂)

private def v₁ : Vect Nat 2 := .cons 1 <| .cons 2 <| .nil
private def v₂ : Vect Nat 1 := .cons 1 <| .nil
private def v₃ : Vect Nat 3 := Vect.nil |>.cons 1 |>.cons 2 |>.cons 3
#eval v₁.append v₂
