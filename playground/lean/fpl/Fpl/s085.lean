import Fpl.Data.Vect

namespace Notes

def Nat.plusL
: Nat → Nat → Nat
| 0, k => k
| n + 1, k => Nat.plusL n k + 1

def Nat.plusR
: Nat → Nat → Nat
| k, 0 => k
| k, n + 1 => Nat.plusR k n + 1

-- def appendL
-- : (n : Nat) → (k : Nat) → Vect α n → Vect α k → Vect α (Nat.plusL n k)
-- | 0, k, .nil, ys => ys
-- | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys : Vect α (Nat.plusL n k))
def appendL
: Vect α n₁ → Vect α n₂ → Vect α (Nat.plusL n₁ n₂)
| .nil, l₂ => l₂
| .cons x₁ l₁', l₂ => .cons x₁ (appendL l₁' l₂)

def plusR_zero_left : (n : Nat) → n = Nat.plusR 0 n
| 0 => by rfl
| n' + 1 => congrArg (· + 1) (plusR_zero_left n')
-- Hey guys, look at this error!!!!
-- And you will understand what is `congrArg`!!!!
-- | n + 1 => plusR_zero_left n

def plusR_succ_left
: (n₁ : Nat) → (n₂ : Nat) → Nat.plusR n₁ n₂ + 1 = Nat.plusR (n₁ + 1) n₂
| n₁, 0 => by rfl
| n₁, n₂' + 1 => congrArg (· + 1) (plusR_succ_left n₁ n₂')

-- def appendR
-- : (n₁ : Nat) → (n₂ : Nat) →  Vect α n₁ → Vect α n₂ → Vect α (Nat.plusR n₁ n₂)
-- | 0, n₂, .nil, l₂ => plusR_zero_left n₂ ▸ l₂
-- | n₁' + 1, n₂, .cons x₁ l₁', l₂ => plusR_succ_left n₁' n₂ ▸
--   .cons x₁ (appendR n₁' n₂ l₁' l₂)
def appendR
: Vect α n₁ → Vect α n₂ → Vect α (Nat.plusR n₁ n₂)
| .nil, l₂ => plusR_zero_left n₂ ▸ l₂
| .cons x₁ l₁', l₂ => plusR_succ_left _ n₂ ▸ .cons x₁ (appendR l₁' l₂)

end Notes

namespace Exercises

def plusL
: Nat → Nat → Nat
| 0, n₂ => n₂
| n₁' + 1, n₂ => n₁' + n₂ + 1
def plusR
: Nat → Nat → Nat
| n₁, 0 => n₁
| n₁, n₂' + 1 => plusR n₁ n₂' + 1

/-!
* Using a recursive function in the style of `plusR_succ_left`, prove that for
all `Nat`s `n` and `k`, `n.plusR k = n + k`.
-/

def plusR_hAdd
: (n₁ : Nat) → (n₂ : Nat) → plusR n₁ n₂ = n₁ + n₂
| n₁, 0 => by rfl
| n₁, n₂' + 1 => congrArg (· + 1) (plusR_hAdd n₁ n₂')

/-!
* Write a function on `Vect` for which `plusR` is more natural than `plusL`,
where `plusL` would require proofs to be used in the definition.
-/

def appendR'
: Vect α n₁ → Vect α n₂ → Vect α (plusR n₁ n₂)
| v₁, .nil => v₁
| v₁, .cons y₁ v₂' => .cons y₁ (appendR' v₁ v₂')

end Exercises
