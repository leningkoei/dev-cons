namespace Note

inductive Option (α : Type u) : Type u where
| none : Option α
| some : α → Option α

class Functor (f : Type u → Type v) : Type (max (u + 1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  -- mapConst : {α β : Type u} → α → f β → f α := λ a mb ↦ map (Function.const _ a) mb
  -- mapConst : {α β : Type u} → α → f β → f α := λ a ↦ map (Function.const _ a)
  -- mapConst : {α β : Type u} → α → f β → f α := map ∘ (λ a ↦ Function.const _ a)
  mapConst : {α β : Type u} → α → f β → f α := map ∘ (Function.const _)

#eval Function.const _ 10 true

def Option.map : (α → β) → Option α → Option β
| _f, none => none
| f, some a => Option.some ∘ f <| a
-- instance : Functor Option where
--   map := Option.map

class Applicative (f : Type u → Type v)
extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map f ma := (pure f) <*> ma
  -- seqRight ma mb := pure (λ _ma' mb' ↦ mb') <*> ma <*> mb ()
  seqRight ma mb := pure (Function.const _ id) <*> ma <*> mb ()
  -- seqLeft ma mb := pure (λ ma' _mb' ↦ ma') <*> ma <*> mb ()
  seqLeft ma mb := pure (Function.const _) <*> ma <*> mb ()

def Option.pure : α → Option α := Option.some
def Option.seq : Option (α → β) → (Unit → Option α) → Option β
| Option.none, _ma => Option.none
| Option.some f, ma =>
  match ma () with
  | Option.none => Option.none
  | Option.some a => Option.some ∘ f <| a
-- instance : Applicative Option where
--   pure := Option.pure
--   seq := Option.seq

class Monad (m : Type u → Type v)
extends Applicative m, Bind m where
  -- seq mf ma := Bind.bind mf (λ f ↦ Bind.bind (ma ()) (λ a ↦ Pure.pure ∘ f <| a))
  seq mf ma := Bind.bind mf (λ f ↦ Functor.map f (ma ()))
  map f ma := Bind.bind ma (λ a ↦ Pure.pure ∘ f <| a)

def Option.bind : Option α → (α → Option β) → Option β
| Option.none, _f => Option.none
| Option.some a, f => f a
instance : Monad Option where
  bind := Option.bind
  pure := Option.pure

end Note
