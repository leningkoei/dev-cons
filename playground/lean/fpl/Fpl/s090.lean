import Fpl.Data.BinTree
import Fpl.Data.Vect

namespace Notes

def plusR
: Nat → Nat → Nat
| n₁, 0 => n₁
| n₁, n₂' + 1 => plusR n₁ n₂' + 1

theorem plusR_zero_left (n : Nat) : n = plusR 0 n := by
  induction n with
  | zero =>
    -- rfl
    simp [plusR]
  | succ n' ih =>
    -- unfold plusR
    -- rw [← ih]
    simp [plusR]
    -- exact ih
    assumption

def BinTree.count
: BinTree α → Nat
| .leaf => 0
| .branch l _ r => 1 + count l + count r

theorem BinTree.mirror_count (t : BinTree α)
: (BinTree.count t.mirror) = BinTree.count t := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    -- simp [BinTree.mirror]
    -- simp [BinTree.count]
    -- -- rw [ihl, ihr]
    -- simp [*]
    -- simp_arith
    simp_arith [BinTree.mirror, BinTree.count, *]

end Notes

namespace Exercises

/-!
1. Prove `plusR_succ_left` using the `induction ... with` tactic.
2. Rewrite the proof of `plusR_succ_left` to use `<;>` in a single line.
-/

def plusR
: Nat → Nat → Nat
| n₁, 0 => n₁
| n₁, n₂' + 1 => plusR n₁ n₂' + 1

theorem plusR_succ_left (n₁ : Nat) (n₂ : Nat)
: plusR n₁ n₂ + 1 = plusR (n₁ + 1) n₂ := by
  induction n₂ with
  | zero =>
    simp [plusR]
  | succ n₂' ihn₂' =>
    simp [plusR]
    -- rw [ihn₂']
    -- exact ihn₂'
    assumption
  -- induction n₂ <;> simp [plusR, *]

/-!
3. Prove that appending lists is associative using induction on lists:
```
theorem List.append_assoc (xs ys zs : List α) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
```
-/

theorem List.append_assoc (xs ys zs : List α) :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  -- simp
  induction xs with
  | nil => simp [List.append]
  | cons x₁ xs' ihxs' => simp [List.append]

end Exercises
