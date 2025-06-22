inductive Many α where
| none : Many α
| more : α → (Unit → Many α) → Many α
deriving Nonempty

def Many.head?
: Many α → Option α
| Many.none => Option.none
| Many.more a _as => Option.some a

def Many.toList
: Many α → List α
| Many.none => []
| Many.more a as => a :: Many.toList (as ())

def Many.take
: Nat → Many α → Many α
| 0, _ => Many.none
| _, Many.none => Many.none
| n, Many.more a as => Many.more a (λ () ↦ (Many.take (n - 1) (as ())))

def Many.union
: Many α → Many α → Many α
| ma, mb =>
  match ma with
  | Many.none => mb
  | Many.more a as => Many.more a (λ () ↦ (Many.union (as ()) mb))

def Many.zipWith
: (α₁ → α₂ → α₃) → Many α₁ → Many α₂ → Many α₃
| _, Many.none, _ => Many.none
| _, _, Many.none => Many.none
| f, Many.more a₁ a₁s, Many.more a₂ a₂s =>
  Many.more (f a₁ a₂) (λ () ↦ (Many.zipWith f (a₁s ()) (a₂s ())))

def Many.filter
: (α → Bool) → Many α → Many α
| _, Many.none => Many.none
| f, Many.more a as =>
  if f a
  then Many.more a (λ () ↦ Many.filter f (as ()))
  else Many.filter f (as ())

def Many.map
: (α → β) → Many α → Many β
| _, Many.none => Many.none
| f, Many.more a as => Many.more (f a) (λ () ↦ Many.map f (as ()))
instance : Functor Many where
  map := Many.map

def Many.pure
: α → Many α
| a => Many.more a (λ () ↦ Many.none)
def Many.seq
: Many (α → β) → (Unit → Many α) → Many β
| Many.none, _ => Many.none
| Many.more f fs, ma =>
  match ma () with
  | Many.none => Many.none
  | Many.more x xs => Many.more (f x) (λ () ↦ Many.seq (fs ()) xs)
instance : Applicative Many where
  pure := Many.pure
  seq := Many.seq

def Many.orElse
: Many α → (Unit → Many α) → Many α
| Many.none, mb => mb ()
| Many.more a as, mb => Many.more a (λ () ↦ Many.orElse (as ()) mb)
instance : Alternative Many where
  failure := Many.none
  orElse := Many.orElse

#eval (
  Many.more 9 (λ () ↦ Many.more 8 (λ () ↦ Many.more 7 (λ () ↦ Many.none)))
  <|>
  Many.more 1 (λ () ↦ Many.more 2 (λ () ↦ Many.more 3 (λ () ↦ Many.none)))
).toList

def Many.bind
: Many α → (α → Many β) → Many β
| ma, f =>
  match ma with
  | Many.none => Many.none
  -- | Many.more a as => (f a).union (Many.bind (as ()) f)
  | Many.more a as =>
    let mb := f a
    let mbs := Many.bind (as ()) f
    mb.union mbs

instance : Monad Many where
  bind := Many.bind

partial def ones : Unit → Many Nat := λ () ↦ Many.more 1 ones
#eval Many.toList ∘ Many.take 1 <| ones ()

partial def nats : Unit → Many Nat := λ () ↦
  Many.more 0 (λ () ↦ Many.zipWith HAdd.hAdd (ones ()) (nats ()))
#eval Many.toList ∘ Many.take 10 <| (nats ())

#eval Many.head? ∘
  Many.filter (λ n ↦
    n > 5 &&
    (n - 2) % 6 == 0 &&
    (n - 4) % 8 == 0 &&
    (n - 5) % 9 == 0
  ) <|
  (nats ())
#eval [0, 1, 2].filter (λ n ↦ (n - 2) % 6 == 0)
#eval [-1, 0, 1, 2].filter (λ n ↦ (n - 2) % 6 == 0)
#eval 0 - 2
