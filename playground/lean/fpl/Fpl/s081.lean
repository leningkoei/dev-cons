namespace Notes

inductive Vect (α : Type u) : Nat → Type u where
| nil : Vect α 0
| cons : α → Vect α n → Vect α (n + 1)

-- def Vect.replicate (n : Nat)
-- : α → Vect α n
def Vect.replicate
: (n : Nat) → α → Vect α n
| n, x =>
  match n with
  | 0 => Vect.nil
  | k + 1 => Vect.cons x (Vect.replicate k x)

def Vect.zip
: Vect α n → Vect β n → Vect (α × β) n
| Vect.nil, Vect.nil => Vect.nil
| Vect.cons a as, Vect.cons b bs =>
  Vect.cons (a, b) (Vect.zip as bs)

end Notes

namespace Exercises

/-!
Getting a feel for programming with dependent types requires experience, and the
exercises in this section are very important. For each exercise, try to see
which mistakes the type checker can catch, and which ones it can't, by
experimenting with the code as you go. This is also a good way to develop a feel
for the error messages.
-/

inductive Vect (α : Type u) : Nat → Type u where
| nil : Vect α 0
| cons : α → Vect α n → Vect α (n + 1)

def Vect.zip
: Vect α n → Vect β n → Vect (α × β) n
| Vect.nil, Vect.nil => Vect.nil
| Vect.cons a as, Vect.cons b bs =>
  Vect.cons (a, b) (Vect.zip as bs)

/-!
* Double-check that `Vect.zip` gives the right answer when combining the three
highest peaks in Oregon with the three highest peaks in Denmark. Because `Vect`
doesn't have the syntactic suger that `List` has, it can be helpful to begin by
defining `oregonianPeaks : Vect String 3` and `danishPeaks : Vect String 3`.
-/

def oregonianPeaks : Vect String 3 :=
  Vect.cons "a" <|
  Vect.cons "b" <|
  Vect.cons "c" <|
  Vect.nil

def danishPeaks : Vect String 3 :=
  Vect.cons "α" <|
  Vect.cons "β" <|
  Vect.cons "γ" <|
  Vect.nil

#eval Vect.zip oregonianPeaks danishPeaks

/-!
* Define a function `Vect.map` with type `(α → β) → Vect α n → Vect β n`.
-/

def Vect.map
: (α → β) → Vect α n → Vect β n
| _, Vect.nil => Vect.nil
| f, Vect.cons a as => Vect.cons (f a) (Vect.map f as)

/-!
* Define a function `Vect.zipWith` that combines the entries in a `Vect` one at
a time with a function. It should have the type
`(α → β → γ) → Vect α n → Vect β n → Vect γ n`.
-/

def Vect.zipWith
: (α → β → γ) → Vect α n → Vect β n → Vect γ n
| _, Vect.nil, Vect.nil => Vect.nil
| f, Vect.cons a as, Vect.cons b bs => Vect.cons (f a b) (Vect.zipWith f as bs)

/-!
* Define a function `Vect.unzip` that splits a `Vect` of pairs into a pair of
`Vect`s. It should have the type `Vect (α × β) n → Vect α n × Vect β n`.
-/

def Vect.unzip
: Vect (α × β) n → Vect α n × Vect β n
| Vect.nil => (Vect.nil, Vect.nil)
| Vect.cons (a, b) abs =>
  let (as, bs) := Vect.unzip abs
  (Vect.cons a as, Vect.cons b bs)

/-!
* Define a function `Vect.push` that adds an entry to the *end* of a `Vect`. Its
type should be `Vect α n → α → Vect α (n + 1)` and
`#eval Vect.push (.cons "snowy" .nil) "peaks"` should yield
`Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil))`.
-/

def Vect.push
: Vect α n → α → Vect α (n + 1)
| Vect.nil, a => Vect.cons a Vect.nil
| Vect.cons b bs, a => Vect.cons b (Vect.push bs a)
#eval Vect.push (.cons "snowy" .nil) "peaks"

/-!
* Define a function `Vect.reverse` that reverses the order of a `Vect`.
-/

def Vect.reverse
: Vect α n → Vect α n
| Vect.nil => Vect.nil
| Vect.cons a as =>
  Vect.push (Vect.reverse as) a

/-!
* Define a function `Vect.drop` with the following type:
`(n : Nat) → Vect α (k + n) → Vect α k`. Verify that it works by checking that
`#eval danishPeaks.drop 2` yields `Vect.cons "Ejer Bavnehøj" (Vect.nil)`.
-/

def Vect.drop
: (n : Nat) → Vect α (k + n) → Vect α k
| 0, vect => vect
| n + 1, Vect.cons _ as => Vect.drop n as
#eval danishPeaks.drop 2

/-!
* Define a function `Vect.take` with type
`(n : Nat) → Vect α (k + n) → Vect α n` that returns the first `n` entries in
the `Vect`. Check that it works on an example.
-/

def Vect.take
: (n : Nat) → Vect α (k + n) → Vect α n
| 0, _ => Vect.nil
| n + 1, Vect.cons a as => Vect.cons a (Vect.take n as)
#eval danishPeaks.take 2

end Exercises
