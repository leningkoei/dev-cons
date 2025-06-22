import Fpl.Data.Date

inductive DBType where
| int
| string
| bool
| date
deriving Repr

abbrev DBType.asType : DBType → Type
| .int => Int
| .string => String
| .bool => Bool
| .date => Date

structure NDBType where
  underlying : DBType
  nullable : Bool
deriving Repr

abbrev NDBType.asType : NDBType → Type
| t =>
  if t.nullable
    then Option t.underlying.asType
    else t.underlying.asType

-- instance

def DBType.beq
: (t : DBType) → t.asType → t.asType → Bool
| t, x, y =>
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
  | .date => x == y
instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance : BEq DBType where
  beq
  | .int, .int => .true
  | .string, .string => .true
  | .bool, .bool => .true
  | .date, .date => .true
  | _, _ => .false

def NDBType.beq
: (t : NDBType) → t.asType → t.asType → Bool
| t, x, y =>
  match t with
  | ⟨t', .true⟩ =>
    let x' : Option t'.asType := x
    let y' : Option t'.asType := y
    x' == y'
  | ⟨t', .false⟩ =>
    let x' : t'.asType := x
    let y' : t'.asType := y
    x' == y'
instance {t : NDBType} : BEq t.asType where
  beq := t.beq

instance : BEq NDBType where
  beq x y := x.nullable == y.nullable && x.underlying == y.underlying

-- example

#eval DBType.int
