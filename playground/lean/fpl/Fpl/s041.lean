inductive Pos : Type where
| one : Pos
| succ : Pos → Pos

def Pos.plus : Pos → Pos → Pos
| Pos.one, k => Pos.succ k
| Pos.succ n, k => Pos.succ (n.plus k)

instance : OfNat Pos (Nat.succ n) where
ofNat := natPlusOne n
  where
  natPlusOne : Nat → Pos
  | 0 => Pos.one
  | k + 1 => Pos.succ (natPlusOne k)

namespace Exercise

/- Another Representation
An alternativer way to represent a positive number is as the successor of some
`Nat`. Replace the definition of `Pos` with a structure whose constructor is
named `succ` that contains a `Nat`:
> structure Pos where
>   succ ::
>   pred : Nat
Define instance of `Add`, `Mul`, `ToString`, and `OfNat` that allow this version
of `Pos` to be used conveniently.
-/

structure Pos where succ ::
  pred : Nat

#eval Pos.succ 2

instance : Add Pos where
  add | Pos.succ x, Pos.succ y => Pos.succ <| x + y + 1

-- #eval (1 : Pos) + (2 : Pos)

instance : Mul Pos where
  mul | Pos.succ x, Pos.succ y => Pos.succ <| (x + 1) * (y + 1) - 1

-- instance : ToString Pos where
--   toString | Pos.succ x => s!"{x + 1}"

def Pos.toNat : Pos → Nat
| Pos.succ n => n + 1

instance : ToString Pos where
  toString := toString ∘ Pos.toNat

instance : OfNat Pos (Nat.succ n) where
  ofNat := Pos.succ n

#eval (1 : Pos) + (2 : Pos)

/- Even Numbers
Define a datatype that represents only even numbers. Define instances of `Add`,
`Mul`, and `ToString` that allow it to be used conveniently. `OfNat` requires a
feature that is introduced in *the next section*.
-/

inductive Even : Type where
| zero : Even
| succ2 : Even → Even

def Even.plus : Even → Even → Even
| Even.zero, y => y
| Even.succ2 x, y => Even.succ2 <| x.plus y

def Even.two := Even.succ2 Even.zero
def Even.four := Even.succ2 Even.two

#eval Even.two.plus Even.four

instance : Add Even where
  add := Even.plus
  -- add
  -- | Even.zero, y => y
  -- | Even.succ2 x, y => Even.succ2 <| x + y

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

/- HTTP Request
An HTTP request begins with an identification of a HTTP method, such as `GET` or
`POST`, along with a URI and an HTTP version. Define an inductive type that
represents an interesting subset of the HTTP methods, and a structure that
represents HTTP responses. Responses should have a `ToString` instance that
makes it possible to debug them. Use a type class to associate different `IO`
actions with each HTTP method, and write a test harness as an `IO` action that
calls each method and prints the result.
-/

namespace HTTP

inductive Method where
| get : Method
| post : Method

structure Request where
  method : Method
  uri : String

structure Response where
  statusCode : Int
  body : String

end HTTP

end Exercise
