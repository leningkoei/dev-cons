namespace Notes

-- In particular, an inductive type may have the same universe level as a
-- parameter, but it must be in a larger universe than its indices.
inductive Vect (α : Type u) : Nat → Type u where
--             parameters --^-- indices
-- Generally speaking, the definition of an inductive type takes its parameters
-- before a colon and its indices after the colon.
| nil : Vect α 0
| cons : α → Vect α n → Vect α (n + 1)

end Notes
