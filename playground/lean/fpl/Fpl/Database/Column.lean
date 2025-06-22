import Fpl.Database.DBType

structure Column : Type u where
  name : String
  -- dbtype : DBType
  dbtype : NDBType
deriving Repr

-- example
