namespace Notes

inductive NatOrBool where
| nat : NatOrBool
| bool : NatOrBool

abbrev NatOrBool.asType
: NatOrBool → Type
| t =>
  match t with
  | NatOrBool.nat => Nat
  | NatOrBool.bool => Bool

def decode
: (t : NatOrBool) → String → Option t.asType
| t, input =>
  match t with
  | NatOrBool.nat => input.toNat?
  | NatOrBool.bool =>
    match input with
    | "true" => Option.some Bool.true
    | "false" => Option.some Bool.false
    | _ => Option.none

inductive Finite where
| unit : Finite
| bool : Finite
| pair : Finite → Finite → Finite
| arr : Finite → Finite → Finite

abbrev Finite.asType
: Finite → Type
| Finite.unit => Unit
| Finite.bool => Bool
| Finite.pair t1 t2 => Finite.asType t1 × Finite.asType t2
| Finite.arr t1 t2 => Finite.asType t1 → Finite.asType t2

def List.product
: List α → List β → List (α × β)
| as, bs => Id.run do
  let mut out : List (α × β) := []
  for a in as do
    for b in bs do
      out := (a, b) :: out
  pure out.reverse
#eval List.product [1,2,3,4] [5,6,7,8]

mutual
  def Finite.functions
  : (t : Finite) → List α → List (t.asType → α)
  | Finite.unit, results =>
    results.map λ result ↦
      λ () ↦ result
  | Finite.bool, results =>
    (List.product results results).map λ (result1, result2) ↦
      λ | Bool.true => result1
        | Bool.false => result2
  | Finite.pair t1 t2, results =>
    let fls := t1.functions ∘ t2.functions <| results
    fls.map λ f ↦
      λ (a, b) ↦ f a b
  | Finite.arr t1 t2, results =>
    let args := t1.enumerate
    let base := results.map λ r ↦ λ _ => r
    args.foldr
      (λ arg rest =>
        (t2.functions rest).map λ more ↦
          λ f ↦ more (f arg) f)
      base

  /-- Enumerate all possible values whose type is `t` --/
  def Finite.enumerate
  : (t : Finite) → List t.asType
  | Finite.unit => [()]
  | Finite.bool => [Bool.true, Bool.false]
  | Finite.pair t1 t2 => List.product t1.enumerate t2.enumerate
  | Finite.arr t1 t2 => t1.functions t2.enumerate
end

def Finite.beq
: (t : Finite) → t.asType → t.asType → Bool
| Finite.unit, _, _ => Bool.true
| Finite.bool, x, y => x == y
| Finite.pair t1 t2, (x1, x2), (y1, y2) =>
  Finite.beq t1 x1 y1 && Finite.beq t2 x2 y2
| Finite.arr t1 t2, x, y =>
  let resultsOfX := List.map x t1.enumerate
  let resultsOfY := List.map y t1.enumerate
  let resultsOfXAndY := List.zipWith (Finite.beq t2) resultsOfX resultsOfY
  (resultsOfXAndY.filter (λ isEqual ↦ not isEqual)) == []
  -- t1.enumerate.all λ arg ↦ Finite.beq t2 (x arg) (y arg)

end Notes

namespace Exercises

/-!
* Write a function that converts any value from a type coded for by `Finite`
into a string. Functions should be represented as their tables.
* Add the empty type `Empty` to `Finite` and `Finite.beq`.
* Add `Option` to `Finite` and `Finite.beq`.
-/

def Matrix.flat
: List (List α) → List α
| [] => []
| [] :: ass => Matrix.flat ass
| (a :: as) :: ass => a :: Matrix.flat (as :: ass)
#eval Matrix.flat [[1,2,3,4],[5,6,7,8]]

def List.product
: List α → List β → List (α × β)
| as, bs => Matrix.flat (List.map (λ a ↦ sum a bs) as)
where
  sum : α → List β → List (α × β)
  | _, [] => []
  | a, b :: bs => (a, b) :: sum a bs
#eval List.product [1,2,3,4] [5,6,7,8] == Notes.List.product [1,2,3,4] [5,6,7,8]

inductive Finite where
| unit : Finite
| bool : Finite
| pair : Finite → Finite → Finite
| function : Finite → Finite → Finite
| empty : Finite
| option : Finite → Finite

abbrev Finite.asType : Finite → Type
| Finite.unit => Unit
| Finite.bool => Bool
| Finite.pair t1 t2 => t1.asType × t2.asType
| Finite.function t1 t2 => t1.asType → t2.asType
| Finite.empty => Empty
| Finite.option t => Option t.asType

mutual

def Finite.functions
: (t : Finite) → List α → List (t.asType → α)
| Finite.unit, results => results.map (λ result ↦ λ () ↦ result)
| Finite.bool, results =>
  (List.product results results).map λ (result1, result2) ↦
    λ | Bool.true => result1
      | Bool.false => result2
| Finite.pair t1 t2, results =>
  (t1.functions ∘ t2.functions <| results).map Function.uncurry
| Finite.function t1 t2, results =>
  let args := t1.enumerate
  let base := results.map λ result ↦ λ _ ↦ result
  args.foldr
    (λ arg rest ↦ (t2.functions rest).map λ more ↦
      λ f ↦ more (f arg) f)
    base
| Finite.empty, _ => []
| Finite.option t, results =>
  (List.product (t.functions results) results).map λ (f, a) ↦
    λ | Option.none => a
      | Option.some a => f a

def Finite.enumerate
: (t : Finite) → List t.asType
| Finite.unit => [()]
| Finite.bool => [Bool.true, Bool.false]
| Finite.pair t1 t2 => List.product t1.enumerate t2.enumerate
| Finite.function t1 t2 => t1.functions t2.enumerate
| Finite.empty => []
| Finite.option t => Option.none :: t.enumerate.map Option.some

end
#eval Finite.enumerate Finite.unit
#eval Finite.enumerate Finite.bool
#eval Finite.enumerate (Finite.pair Finite.unit Finite.unit)
#eval (Finite.enumerate
  (Finite.function
    (Finite.pair Finite.bool Finite.bool)
    Finite.bool
  )).length

def Finite.beq
: (t : Finite) → t.asType → t.asType → Bool
| Finite.unit, _, _ => Bool.true
| Finite.bool, x, y => x == y
| Finite.pair t1 t2, (x1, x2), (y1, y2) =>
  Finite.beq t1 x1 y1 && Finite.beq t2 x2 y2
| Finite.function t1 t2, f1, f2 =>
  let xs := t1.enumerate
  let y1s := List.map f1 xs
  let y2s := List.map f2 xs
  let eqs := List.zipWith (Finite.beq t2) y1s y2s
  List.filter (λ isEq ↦ not isEq) eqs == []
| Finite.option t, x, y =>
  match x, y with
  | Option.none, Option.none => Bool.true
  | Option.none, _ => Bool.false
  | _, Option.none => Bool.false
  | Option.some x, Option.some y => Finite.beq t x y

def Finite.toString
: (t : Finite) → t.asType → String
| Finite.unit, _ => "()"
| Finite.bool, Bool.true => "true"
| Finite.bool, Bool.false => "false"
| Finite.pair t1 t2, (v1, v2) => s!"({t1.toString v1}, {t2.toString v2})"
| Finite.function t1 t2, f =>
  let fuck := t1.enumerate.map
    (λ v1 ↦ s!"if argument == {t1.toString v1} then result := {t2.toString (f v1)}")
  join fuck "\n"
| Finite.option _, Option.none => "none"
| Finite.option t, Option.some v => s!"some {t.toString v}"
where
  join : List String → String → String
  | [], _ => ""
  | [a], _ => a
  | a :: as, string => a ++ string ++ join as string

#eval Finite.toString Finite.unit ()
#eval Finite.toString Finite.bool Bool.false
#eval Finite.toString
  (Finite.pair Finite.bool Finite.bool) (Bool.true, Bool.false)
#eval IO.print <| Finite.toString
  (Finite.function (Finite.pair Finite.bool Finite.bool) Finite.bool)
  λ | (true, true) => Bool.false
    | (true, false) => Bool.true
    | (false, true) => Bool.false
    | (false, false) => Bool.true
#eval Finite.toString (Finite.option Finite.bool) (Option.some Bool.true)
#eval IO.print <| Finite.toString
  (Finite.function (Finite.option Finite.bool) Finite.bool)
  λ | Option.none => Bool.false
    | Option.some x => x

end Exercises
