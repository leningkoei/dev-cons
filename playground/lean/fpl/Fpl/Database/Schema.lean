import Fpl.Database.Column

abbrev Schema : Type := List Column

-- inductive TheCol : Schema → String → DBType → Type where
inductive TheCol : Schema → String → NDBType → Type where
| here : TheCol (⟨name, dbtype⟩ :: _) name dbtype
| there : TheCol schema name dbtype → TheCol (_ :: schema) name dbtype

inductive Subschema : Schema → Schema → Type where
| nil : Subschema [] schema
| cons :
  TheCol bigger name dbtype →
  Subschema smaller bigger →
  Subschema (⟨name, dbtype⟩ :: smaller) bigger

-- method

def Schema.renameColumn
: (s : Schema) → (c : TheCol s n t) → (n' : String) → Schema
| c :: cs, .here, n' => {c with name := n'} :: cs
| c :: cs, .there next, n' => c :: renameColumn cs next n'

def Subschema.addColumn
: Subschema smaller bigger → Subschema smaller (col :: bigger)
| subschema =>
  match subschema with
  | .nil => .nil
  | .cons col subschema => .cons (.there col) subschema.addColumn

def Subschema.reflexive
: (schema : Schema) → Subschema schema schema
| [] => .nil
| _::schema => .cons .here (reflexive schema).addColumn

-- example

-- abbrev peak : Schema :=
--   [ ⟨"name", .string⟩
--   , ⟨"location", .string⟩
--   , ⟨"elevation", .int⟩
--   , ⟨"lastVisitedDate", .date⟩
--   ]
--
-- abbrev waterfall : Schema :=
--   [ ⟨"name", .string⟩
--   , ⟨"location", .string⟩
--   , ⟨"lastVisitedDate", .date⟩
--   ]
--
-- abbrev travelDiary : Schema :=
--   [ ⟨"name", .string⟩,
--   ⟨"location", .string⟩,
--   ⟨"lastVisitedDate", .date⟩ ]

abbrev peak : Schema :=
  [ ⟨"name", ⟨.string, .false⟩⟩
  , ⟨"location", ⟨.string, .false⟩⟩
  , ⟨"elevation", ⟨.int, .true⟩⟩
  , ⟨"lastVisitedDate", ⟨.date, .false⟩⟩
  ]

abbrev waterfall : Schema :=
  [ ⟨"name", ⟨.string, .false⟩⟩
  , ⟨"location", ⟨.string, .false⟩⟩
  , ⟨"lastVisitedDate", ⟨.date, .false⟩⟩
  ]

abbrev travelDiary : Schema :=
  [ ⟨"name", ⟨.string, .false⟩⟩,
  ⟨"location", ⟨.string, .false⟩⟩,
  ⟨"lastVisitedDate", ⟨.date, .false⟩⟩ ]

example : Subschema travelDiary peak :=
  (.cons .here -- name
    (.cons (.there .here) -- location
      (.cons (.there (.there (.there .here))) -- lastVisitedDate
        .nil)))
example : Subschema travelDiary peak := by repeat constructor

abbrev userinfoS : Schema :=
  [ ⟨"username", ⟨.string, .false⟩⟩
  , ⟨"age", ⟨.int, .false⟩⟩
  , ⟨"birthday", ⟨.date, .false⟩⟩
  ]

def elevation : TheCol peak "elevation" ⟨.int, .true⟩ := .there <| .there <| .here
