import Lean
import Fpl.Data.NonEmptyList
import Fpl.Data.Pos

namespace Note

-- class Coe (α : Type) (β : Type) where
--   coe : α → β
-- class CoeDep (α : Type) (x : α) (β : Type) where
--   coe : β

-- class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
--   coe : (x : α) → makeFunctionType x

instance : Coe Pos Nat where
  coe x := x.toNat
#eval [1, 2, 3, 4].drop (2 : Pos)

instance : Coe (NonEmptyList α) (List α) where
  coe
    | nonEmptyList => nonEmptyList.head :: nonEmptyList.tail
#check List.drop
#eval (List.drop : Nat → List Nat → List Nat) (2 : Pos) (NonEmptyList.mk 1 [2, 3, 4])

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := NonEmptyList.mk x xs
#eval (NonEmptyList.head : NonEmptyList Nat → Nat) [1, 2, 3, 4]

structure Monoid where
  Carrier: Type
  neutral: Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid := {
  Carrier := Nat,
  neutral := 1,
  op := (· * ·),
}

def natAddMonoid : Monoid := {
  Carrier := Nat,
  neutral := 0,
  op := (· + ·),
}

def stringMonoid : Monoid := {
  Carrier := String,
  neutral := "",
  op := String.append,
}

def listMonoid : (α : Type) → Monoid
| α => {
  Carrier := List α,
  neutral := [],
  op := List.append,
}

instance : CoeSort Monoid Type where
  coe m := m.Carrier

-- def foldMap : (M : Monoid) → (α → M.Carrier) → List α → M.Carrier
def foldMap : (M : Monoid) → (α → M) → List α → M
| M, f, xs => go M f M.neutral xs
where
  go : (M : Monoid) → (α → M.Carrier) → M.Carrier → List α → M.Carrier
  | _M, _f, soFar, [] => soFar
  | M, f, soFar, x :: xs => go M f (M.op soFar (f x)) xs

structure Adder where
  howMuch : Nat

def add5 : Adder := Adder.mk 5
#eval add5

instance : CoeFun Adder (λ _Adder => Nat → Nat) where
  coe a := (· + a.howMuch)
#eval add5 3

inductive JSON where
| true : JSON
| false : JSON
| null : JSON
| string : String → JSON
| number : Float → JSON
| array : List JSON → JSON
| object : List (String × JSON) → JSON

structure JSON.Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str : JSON.Serializer := {
  Contents := String,
  serialize := JSON.string,
}

instance : CoeFun JSON.Serializer (λ s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse : String → (R : JSON.Serializer) → R.Contents → JSON
| title, R, record => JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    -- ("record", R.serialize record),
    ("record", R record),
  ]
#eval buildResponse "Function Programming in Lean" Str "Programming is fun"

partial def JSON.asString (val : JSON) : String :=
  let dropDecimals (s : String) : String :=
    let s := s.dropRightWhile (· == '0')
    match s.back with
    | '.' => s.dropRight 1
    | _ => s
  let rec appendWith (xs : List String) (y : String) : String :=
    match xs with
    | [] => ""
    | [x] => x
    | x :: xs => (x ++ y) ++ appendWith xs y
  match val with
  | JSON.true => "true"
  | JSON.false => "false"
  | JSON.null => "null"
  | JSON.string s => "\"" ++ Lean.Json.escape s ++ "\""
  | JSON.number n => dropDecimals n.toString
  | JSON.array elements =>
    "[" ++ (appendWith (elements.map JSON.asString) ", ") ++ "]"
  | JSON.object members =>
    let member2string (member : String × JSON) : String :=
      match member with
      | (key, value) => "\"" ++ key ++ "\"" ++ ": " ++ value.asString
    "{" ++ (appendWith (members.map member2string) ", ") ++ "}"

#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString

end Note
