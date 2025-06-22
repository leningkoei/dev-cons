import Fpl.Data.NonEmptyList

namespace Note

instance : Applicative Option where
  pure x := Option.some x
  seq f x :=
    match f with
    | Option.none => Option.none
    | Option.some g => g <$> x ()

def Pos : Type := { x : Nat // x > 0 }
def one : Pos := ⟨1, by simp⟩
instance : OfNat Pos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩
def Nat.asPos? (n : Nat) : Option Pos :=
  if h : n > 0
  then Option.some ⟨n, h⟩
  else Option.none

structure RawInput where
  name : String
  birthYear : String

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ "" }
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

inductive Validate (ε : Type) (α : Type) : Type where
| ok : α → Validate ε α
| errors : NonEmptyList ε → Validate ε α

instance : Functor (Validate ε) where
  map f
  | Validate.ok x => Validate.ok (f x)
  | Validate.errors errors => Validate.errors errors

instance : Applicative (Validate ε) where
  pure := Validate.ok
  seq f x :=
    match f with
    | Validate.ok g => g <$> x ()
    | Validate.errors errors =>
      match x () with
      | Validate.ok _ => Validate.errors errors
      | Validate.errors errors' => Validate.errors <| errors ++ errors'

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  Validate.errors {
    head := (f, msg),
    tail := [],
  }

def checkName (name : String)
: Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = ""
  then reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β)
: Validate ε β :=
  match val with
  | Validate.errors errs => Validate.errors errs
  | Validate.ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | Option.none => reportError "birth year" "Must be digits"
  | Option.some n => pure n

def checkBirthYear (thisYear year : Nat)
: Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900
    then if h' : year ≤ thisYear
      then pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth" "Must be after 1900"
  -- if h : year ≤ 1900
  -- then reportError "birth year" "Must be after 1900"
  -- else if h' : year > thisYear
  -- then reportError "birth year" s!"Must be no later than {thisYear}"
  -- else pure ⟨year, by simp [*]⟩

def checkInput (year : Nat) (input : RawInput)
: Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
  checkName input.name <*>
  (checkYearIsNat input.birthYear).andThen λ birthYearAsNat =>
    checkBirthYear year birthYearAsNat

end Note
