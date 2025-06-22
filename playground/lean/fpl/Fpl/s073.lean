namespace Notes

structure LetterCounts : Type u where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err : Type u where
| notALetter : Char → Err
deriving Repr

def vowels : String := "aeiouy"
def consonants : String := "bcdfghjklmnpqrstvwxz"

def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
: String → m Unit
| string =>
  loop string.toList
where
  loop : List Char → m Unit
  | [] => pure ()
  | c :: cs => do
    if c.isAlpha then
      if vowels.contains c then
        modify λ st ↦ {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify λ st ↦ {st with consonants := st.consonants + 1}
      else
        pure ()
    else
      throw (Err.notALetter c)
    loop cs

abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)

#eval countLetters (m := M1) "hello" ⟨0, 0⟩
#eval countLetters (m := M2) "hello" ⟨0, 0⟩

#eval countLetters (m := M1) "hello12345hello" ⟨0, 0⟩
#eval countLetters (m := M2) "hello12345hello" ⟨0, 0⟩

def countWithFallback [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
: String → m Unit
| string =>
  try countLetters string
  catch _ =>
    countLetters "Fallback"

#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩

#eval countWithFallback (m := M1) "hello12345hello" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello12345hello" ⟨0, 0⟩

end Notes

namespace Exercises

/-!
* Check that `ReaderT` and `StateT` commute by expanding their definitions and
reasoning about the resulting types.
-/

/-!
ReaderT ρ m α := ρ → m α
StateT σ m α := σ → (α × σ)

ReaderT ρ (StateT σ Id) α
==>
ρ → ((StateT ρ Id) α)
==>
ρ → (σ → (α × σ))

StateT σ (ReaderT ρ Id) α
==>
σ → (ReaderT ρ Id (α × σ))
==>
σ → (ρ → (α × σ))
-/

/-!
* Do `ReaderT` and `ExceptT` commute? Check your answer by expanding their
definitions and reasoning about the resulting types.
-/

/-!
ReaderT ρ m α := ρ → m α
ExceptT ε m α := m Except ε α

ReaderT ρ (ExceptT ε Id) α
==>
ρ → ((ExceptT ε Id) α)
==>
ρ → (Except ε α)

ExceptT ε (ReaderT ρ Id) α
==>
(ReaderT ρ Id) (Except ε α)
==>
ρ → (Except ε α)
-/

/-!
* Construct a monad transformer `ManyT` based on the definition of `Many`, with
a suitable `Alternative` instance. Check that it satisfies the `Monad` contract.
-/

inductive Many (α : Type u) : Type u where
| none : Many α
| more : α → (Unit → Many α) → Many α
deriving Nonempty

def Many.union
: Many α → Many α → Many α
| ma, mb =>
  match ma with
  | Many.none => mb
  | Many.more a as =>
    Many.more a (λ () ↦ (as ()).union mb)

def Many.pure
: α → Many α
| a => Many.more a (λ () ↦ Many.none)
def Many.seq
: Many (α → β) → (Unit → Many α) → Many β
| f, ma =>
  match f with
  | Many.none => Many.none
  | Many.more f fs =>
    match ma () with
    | Many.none => Many.none
    | Many.more a as =>
      let b := f a
      let bs := Many.seq (fs ()) as
      Many.more b (λ () ↦ bs)
instance : Applicative Many where
  pure := Many.pure
  seq := Many.seq

def Many.orElse
: Many α → (Unit → Many α) → Many α
| Many.none, mb => mb ()
| ma, mb => ma.union (mb ())
instance : Alternative Many where
  failure := Many.none
  orElse := Many.orElse

abbrev ManyT
: (Type u → Type v) → Type u → Type v
| m, α => m (Many α)
def ManyT.mk : m (Many α) → ManyT m α := id
def ManyT.run : ManyT m α → m (Many α) := id

def ManyT.pure
  [Monad m]
: α → ManyT m α
| a => ManyT.mk (Pure.pure (Many.more a (λ () ↦ Many.none)))
def ManyT.seq
  [Monad m]
: ManyT m (α → β) → (Unit → ManyT m α) → ManyT m β
| f, ma => ManyT.mk do
  let a ← ma ()
  let f ← f.run
  let b := f <*> a
  Pure.pure b
instance [Monad m] : Applicative (ManyT m) where
  pure := ManyT.pure
  seq := ManyT.seq

def ManyT.orElse [Monad m]
: ManyT m α → (Unit → ManyT m α) → ManyT m α
| ma, mb => ManyT.mk do
  let a ← ma.run
  match a with
  | Many.none => mb ()
  | _ =>
    let b ← (mb ()).run
    Pure.pure (a <|> b)
instance [Monad m] : Alternative (ManyT m) where
  failure := ManyT.mk ∘ pure <| Many.none
  orElse := ManyT.orElse

/-- # Why it has to add `partial` -/
partial def ManyT.bind [Monad m]
: ManyT m α → (α → ManyT m β) → ManyT m β
| ma, f => ManyT.mk do
  let a ← ma.run
  match a with
  | Many.none => Pure.pure Many.none
  | Many.more a as =>
    let b ← (f a).run
    let mas : ManyT m α := ManyT.mk ∘ Pure.pure <| as ()
    let bs ← (ManyT.bind mas f).run
    Pure.pure (b.union bs)
instance [Monad m] : Monad (ManyT m) where
  bind := ManyT.bind

/-!
Does `ManyT` commute with `StateT`? If so, check your answer by expanding
definitions and reasoning about the resulting type. If not, write a program in
`ManyT (StateT σ Id)` and a program in `StateT σ (ManyT Id)`. Each program
should be one that makes more sense for the given ordering of monad
transformers.
-/

/-!
StateT σ m α := σ → (α × σ)
ManyT m α := m (Many α)

StateT σ (ManyT Id) α
==>
σ → ((ManyT Id) (α × σ))
==>
σ → (Many (α × σ))

ManyT (StateT σ Id) α
==>
(StateT σ Id) (Many α)
==>
σ → ((Many α) × σ)
-/

end Exercises
