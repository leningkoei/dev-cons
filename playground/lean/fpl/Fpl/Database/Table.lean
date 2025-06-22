import Fpl.Database.Row
import Fpl.Database.Schema

abbrev Table : Schema → Type
-- := List ∘ Row
| schema => List (Row schema)

-- instance

-- exmaple

abbrev mountainDiary : Table peak :=
  [neboDiary, moscowDiary, himmelbjergetDiary, helensDiary]
#eval mountainDiary

abbrev waterfallDiary : Table waterfall := [multnomahDiary, shoshoneDiary]

-- abbrev userinfo : Table userinfoS :=
--   [ ("lening", 24, date!(2001, 08, 15))
--   , ("leningDouble", 48, date!(1977, 08, 15))
--   ]
abbrev userinfo : Table userinfoS :=
  [ ("lening", (24 : Int), date!(2001, 08, 15))
  , ("leningDouble", (48 : Int), date!(1977, 08, 15))
  ]
