inductive MyNat : Type where
| zero : MyNat
| succ : MyNat → MyNat
deriving Repr

notation "ℕ" => MyNat

-- def succ : ℕ → ℕ := MyNat.succ

def ℕ.ofNat
: Nat → ℕ
| .zero => .zero
| .succ a' => .succ (ℕ.ofNat a')

instance : OfNat ℕ 0 where
  ofNat := .zero

instance [OfNat ℕ n] : OfNat ℕ (n + 1) where
  ofNat := .succ (OfNat.ofNat n)

def ℕ.hAdd
: ℕ → ℕ → ℕ
| .zero, b => b
| .succ a', b => .succ (ℕ.hAdd a' b)
instance : HAdd ℕ ℕ ℕ where
  hAdd := ℕ.hAdd

def ℕ.hMul
: ℕ → ℕ → ℕ
| .zero, _ => .zero
-- | _, .zero => .zero
| .succ a', b => b + (ℕ.hMul a' b)
instance : HMul ℕ ℕ ℕ where
  hMul := ℕ.hMul
