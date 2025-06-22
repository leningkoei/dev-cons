import Fpl.Data.NonEmptyList
import Fpl.Data.Many

namespace Note

structure RawInput : Type where
  name : String
  birthYear : String

inductive Validate (ε : Type) (α : Type) : Type where
| ok : α → Validate ε α
| errors : NonEmptyList ε → Validate ε α
deriving Repr

def Validate.map (f : α → β) (a : Validate ε α) : Validate ε β :=
  match a with
  | Validate.ok a => Validate.ok ∘ f <| a
  | Validate.errors msg => Validate.errors msg
instance : Functor (Validate ε) where
  map := Validate.map

def Validate.pure (x : α) : Validate ε α := Validate.ok x
def Validate.seq (f : Validate ε (α → β)) (a : Unit → Validate ε α)
: Validate ε β :=
  match f with
  | Validate.ok g => g <$> a ()
  | Validate.errors msg =>
    match a () with
    | Validate.ok _ => Validate.errors msg
    | Validate.errors msg' => Validate.errors <| msg ++ msg'
instance : Applicative (Validate ε) where
  pure := Validate.pure
  seq := Validate.seq

def Field := String

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput : Type where
| humanBefore1970
: (birthYear : {y : Nat // y > 999 ∧ y < 1970}) → String → LegacyCheckedInput
| humanAfter1970
: (birthYear : {y : Nat // y > 1970}) → NonEmptyString → LegacyCheckedInput
| company : NonEmptyString → LegacyCheckedInput
deriving Repr

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α)
: Validate ε α :=
  match a with
  | Validate.ok x => Validate.ok x
  | Validate.errors errs1 =>
    match b () with
    | Validate.ok x => Validate.ok x
    | Validate.errors errs2 => Validate.errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def reportError (field : Field) (msg : String) : Validate (Field × String) α :=
  Validate.errors [(field, msg)]

#eval (reportError : Field → String → Validate (Field × String) Nat)
  "birth" "FIRM if a company"

def checkName (name : String) : Validate (Field × String) NonEmptyString :=
  if h : name ≠ ""
  then pure ⟨name, h⟩
  else reportError "name" "Required"

def checkCompany (input : RawInput)
: Validate (Field × String) LegacyCheckedInput :=
  if input.birthYear == "FIRM"
  then LegacyCheckedInput.company <$> checkName input.name
  else reportError "birth year" "FIRM if a company"

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | Option.none => reportError "birth year" "Must be digits"
  | Option.some n => pure n

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (msg : ε)
: Validate ε {x : α // p x} :=
  if h : p v
  then pure ⟨v, h⟩
  else Validate.errors { head := msg, tail := [] }

def checkHumanBefore1970 (input : RawInput)
: Validate (Field × String) LegacyCheckedInput :=
  match checkYearIsNat input.birthYear with
  | Validate.errors msg => Validate.errors msg
  | Validate.ok n => LegacyCheckedInput.humanBefore1970
    <$> checkSubtype n (λ x => x > 999 ∧ x < 1970) ("birth year", "Less than 1970")
    <*> pure input.name
  -- | Validate.ok n => if h : n > 999 ∧ n < 1970
  --   then pure <| LegacyCheckedInput.humanBefore1970 ⟨n, h⟩ input.name
  --   else Validate.errors
  --     { head := ("birth year", "Less than 1970"), tail := [] }

def checkHumanAfter1970 (input : RawInput)
: Validate (Field × String) LegacyCheckedInput :=
  match checkYearIsNat input.birthYear with
  | Validate.errors msg => Validate.errors msg
  | Validate.ok n => LegacyCheckedInput.humanAfter1970
    <$> checkSubtype n (λ x => x > 1970) ("birth year", "Greater than 1970")
    <*> checkName input.name

def checkLegacyInput (input : RawInput)
: Validate (Field × String) LegacyCheckedInput
  :=  checkCompany input
  <|> checkHumanBefore1970 input
  <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"John", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"", "1970"⟩

class Alternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α

instance : Alternative Option where
  failure := Option.none
  orElse
  | Option.some x, _ => some x
  | Option.none, y => y ()

-- Fpl.Data.Many

def Many.countdown
: Nat → Many Nat
| 0 => Many.none
| n + 1 => Many.more n (λ () => Many.countdown n)
#eval Many.toList ∘ Many.countdown <| 20

def evenDivisors
: Nat → Many Nat
| n => do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
#eval Many.toList ∘ evenDivisors <| 20

end Note

namespace Exercises

/-! # Improve Validation Friendliness
The errors returned from `Validate` programs that use `<|>` can be difficult to
read, because inclusion in the list of errors simply means that the error can be
reached through *some* code path. A more structured error report can be used to
guide the user throuth the process more accurately:
- Replace the `NonEmptyList` in `Validate.error` with a bare type variable, and
then update the definitions of the `Applicative (Validate ε)` and
`OrElse (Validate ε α)` instances to require only that there be an `Append ε`
instance available.
- Define a function
`Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε α` that transforms
all the errros in a validation run.
- Using the datatype `TreeError` to represent errors, rewrite the legacy
validation system to track its path through the three alternatives.
- Write a function `report : TreeError → String` that outputs a user-friendly
view of the `TreeError`'s accumulated warnings and errors.
```
inductive TreeError where
| field : Field → String → TreeError
| path : String → TreeError → TreeError
| both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
```
-/

inductive Validate (ε : Type) (α : Type) : Type where
| ok : α → Validate ε α
| errors : ε → Validate ε α
deriving Repr

def Validate.map
: (α → β) → Validate ε α → Validate ε β
| f, Validate.ok a => Validate.ok ∘ f <| a
| _f, Validate.errors es => Validate.errors es
instance : Functor (Validate ε) where
  map := Validate.map

def Validate.pure
: α → Validate ε α
| a => Validate.ok a
def Validate.seq
  [Append ε]
: Validate ε (α → β) → (Unit → Validate ε α) → Validate ε β
| Validate.ok f, ma => f <$> ma ()
| Validate.errors es, ma =>
  match ma () with
  | Validate.ok _a => Validate.errors es
  | Validate.errors es' => Validate.errors (es ++ es')
instance [Append ε] : Applicative (Validate ε) where
  pure := Validate.pure
  seq := Validate.seq

def Validate.andThen
: Validate ε α₁ → (α₁ → Validate ε α₂) → Validate ε α₂
| ma₁, f =>
  match ma₁ with
  | Validate.errors es₁ => Validate.errors es₁
  | Validate.ok a₁ => f a₁

def Validate.orElse
  [Append ε]
: Validate ε α → (Unit → Validate ε α) → Validate ε α
| Validate.ok a, _ => Validate.ok a
| Validate.errors es₁, mb =>
  match mb () with
  | Validate.ok b => Validate.ok b
  | Validate.errors es₂ => Validate.errors (es₁ ++ es₂)
instance [Append ε] : OrElse (Validate ε α) where
  orElse := Validate.orElse

def Validate.mapError
: Validate ε₁ α → (ε₁ → ε₂) → Validate ε₂ α
| Validate.ok a, _f => Validate.ok a
| Validate.errors es₁, f => Validate.errors (f es₁)

abbrev Field : Type := String
inductive TreeError where
| field : Field → String → TreeError
| path : String → TreeError → TreeError
| both : TreeError → TreeError → TreeError
deriving Repr

instance : Append TreeError where
  append := TreeError.both

structure RawInput : Type where
  name : String
  birthYear : String

abbrev NonEmptyString : Type := {s : String // s ≠ ""}
inductive LegacyCheckedInput : Type where
| humanBefore1970
: {y : Nat // y > 999 ∧ y < 1970} → String → LegacyCheckedInput
| humanAfter1970
: {y : Nat // y > 1970} → NonEmptyString → LegacyCheckedInput
| company : NonEmptyString → LegacyCheckedInput
deriving Repr

def reportError
  {α : Type}
: String → Field → String → Validate TreeError α
| path, field, msg =>
  Validate.errors ∘
  TreeError.path path <|
  TreeError.field field msg

def checkCompany
: RawInput → Validate TreeError LegacyCheckedInput
| input =>
  if input.birthYear ≠ "FIRM"
  then thisReportError "birth year" "FIRM if a company"
  else if h : input.name ≠ ""
  then Validate.ok (LegacyCheckedInput.company ⟨input.name, h⟩)
  else thisReportError "name" "Required"
where
  thisReportError {α : Type} : Field → String → Validate TreeError α :=
    reportError "company"
#eval checkCompany ⟨"", ""⟩

def checkHumanBefore1970
: RawInput → Validate TreeError LegacyCheckedInput
| input =>
  let checkYear
  : Unit → Validate TreeError {y : Nat // y > 999 ∧ y < 1970}
  := λ () ↦
    match input.birthYear.trim.toNat? with
    | Option.none => thisReportError "birth year" "Must be digits"
    | Option.some year =>
      if h : year > 999 ∧ year < 1970
      then Validate.ok ⟨year, h⟩
      else thisReportError "birth year" "Less than 1970"
  let checkName
  : Unit → Validate TreeError String
  := λ () ↦
    Validate.ok input.name
  let f
  : Validate TreeError
    ({y : Nat // y > 999 ∧ y < 1970} → String → LegacyCheckedInput)
  := pure λ year name => LegacyCheckedInput.humanBefore1970 year name
  f <*> checkYear () <*> checkName ()
where
  thisReportError {α : Type} : Field → String → Validate TreeError α :=
    reportError "human before 1970"
#eval checkHumanBefore1970 ⟨"", ""⟩

def checkHumanAfter1970
: RawInput → Validate TreeError LegacyCheckedInput
| input =>
  let checkYear
  : Unit → Validate TreeError {year : Nat // year > 1970}
  := λ () ↦
    match input.birthYear.trim.toNat? with
    | Option.none => thisReportError "birth year" "Must be digits"
    | Option.some year =>
      if h : year > 1970
      then pure ⟨year, h⟩
      else thisReportError "birth year" "Greater than 1970"
  let checkName
  : Unit → Validate TreeError NonEmptyString
  := λ () ↦
    if h : input.name ≠ ""
    then pure ⟨input.name, h⟩
    else thisReportError "name" "Require"
  let f
  : Validate TreeError
    ({y : Nat // y > 1970} → NonEmptyString → LegacyCheckedInput)
  := pure λ year name ↦ (LegacyCheckedInput.humanAfter1970 year name)
  f <*> checkYear () <*> checkName ()
where
  thisReportError {α : Type} : Field → String → Validate TreeError α :=
    reportError "human after 1970"
#eval checkHumanAfter1970 ⟨"", ""⟩

-- #print Append
-- instance [Append ε] : Alternative (Validate ε) where
--   failure := Validate.errors Empty
--   orElse := OrElse.orElse

def checkLegacyInput
: RawInput → Validate TreeError LegacyCheckedInput
| input
  =>  checkCompany input
  <|> checkHumanAfter1970 input
  <|> checkHumanBefore1970 input
#eval checkLegacyInput ⟨"", "1970"⟩

def report
: TreeError → String
| TreeError.field field msg => s!"({field}: {msg})"
| TreeError.path path es => s!"|- {path} => {report es}"
| TreeError.both (TreeError.path path₁ es₁) (TreeError.path path₂ es₂) =>
  if path₁ == path₂
  then s!"\
|- {path₁}
    |- {report es₁}
    |- {report es₂}"
  else s!"\
{report es₁}
{report es₂}"
| TreeError.both es₁ es₂ => s!"\
{report es₁}
{report es₂}"
#eval
  match checkLegacyInput ⟨"", "1970"⟩ with
  | Validate.ok _ => "wtf"
  | Validate.errors es => report es

def fuck : Validate TreeError Nat := Exercises.Validate.errors
  (Exercises.TreeError.both
    (Exercises.TreeError.path "company" (Exercises.TreeError.field "birth year" "FIRM if a company"))
    (Exercises.TreeError.both
      (Exercises.TreeError.both
        (Exercises.TreeError.path "human after 1970"
          (Exercises.TreeError.both
            (Exercises.TreeError.path "fuck" (Exercises.TreeError.field "shit" "wtf₁"))
            (Exercises.TreeError.path "fuck" (Exercises.TreeError.field "shit" "wtf₂"))))
        (Exercises.TreeError.path "human after 1970" (Exercises.TreeError.field "name" "Require")))
      (Exercises.TreeError.path "human before 1970" (Exercises.TreeError.field "birth year" "Less than 1970"))))
#eval
  match fuck with
  | Validate.ok _ => "wtf"
  | Validate.errors es => report es

end Exercises
