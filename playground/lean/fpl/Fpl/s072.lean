namespace Note

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == ""
  then failure
  else pure trimmed

structure UserInfo where
  name : String
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let favoriteBeetle ← getSomeInput
  pure <| UserInfo.mk name favoriteBeetle

def interact : IO Unit := do
  match ← getUserInfo with
  | Option.none => IO.eprintln "Missing info"
  | Option.some ⟨name, beetle⟩ =>
    IO.println s!"Hello {name}, whose favorite beetle is {beetle}."

namespace OptionT

inductive Option (α : Type u) : Type u where
| none : Option α
| some : α → Option α
def OptionT : (Type u → Type v) → Type u → Type v
| m, α => m (Option α)

def OptionT.mk : m (Option α) → OptionT m α := id
def OptionT.run : OptionT m α → m (Option α) := id

instance : Monad Option where
  pure := Option.some
  bind ma f :=
    match ma with
    | Option.none => Option.none
    | Option.some a => f a

instance [Monad m] : Monad (OptionT m) where
  pure := OptionT.mk ∘ pure ∘ Option.some
  bind ma f := OptionT.mk do
    let oa ← ma.run
    match oa with
    | Option.none => pure Option.none
    | Option.some a => (f a).run

instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk ∘ pure <| Option.none
  orElse ma mb := OptionT.mk do
    match ← ma.run with
    | Option.none => mb ()
    | Option.some a => pure ∘ Option.some <| a

instance [Monad m] : MonadLift Option (OptionT m) where
  monadLift := OptionT.mk ∘ pure

instance [Monad m] : MonadLift m (OptionT m) where
  monadLift := OptionT.mk ∘ Functor.map Option.some

end OptionT

namespace ExceptT

inductive Except (ε : Type e) (α : Type u) : Type (max e u) where
| error : ε → Except ε α
| ok : α → Except ε α
def ExceptT : Type e → (Type (max e u) → Type v) → Type u → Type v
| ε, m, α => m (Except ε α)

def ExceptT.mk : m (Except ε α) → ExceptT ε m α := id
def ExceptT.run : ExceptT ε m α → m (Except ε α) := id

instance [Monad m] : Monad (ExceptT ε m) where
  pure := ExceptT.mk ∘ pure ∘ Except.ok
  bind ma f := ExceptT.mk do
    let ea ← ma.run
    match ea with
    | Except.error msg => pure ∘ Except.error <| msg
    | Except.ok a => (f a).run

instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift := ExceptT.mk ∘ pure

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift := ExceptT.mk ∘ Functor.map Except.ok

end ExceptT

namespace MonadExcept

class MonadExcept (ε : Type e) (m : Type u → Type v)
: Type (max e (u + 1) v) where
  throw : ε → m α
  tryCatch : m α → (ε → m α) → m α

end MonadExcept

inductive Err where
| divByZero : Err
| notANumber : String → Err

def divBackend [Monad m] [MonadExcept Err m]
: Int → Int → m Int
| n, k =>
  if k == 0
  then throw Err.divByZero
  else pure (n / k)

def asNumber [Monad m] [MonadExcept Err m]
: String → m Int
| s =>
  match s.toInt? with
  | Option.none => throw (Err.notANumber s)
  | Option.some i => pure i

def divFrontend [Monad m] [MonadExcept Err m]
: String → String → m String
| n, k => do
  let n ← asNumber n
  let k ← asNumber k
  let result := toString <$> divBackend n k
  -- tryCatch result
  --   λ | Err.divByZero => pure "Division by zero!"
  --     | Err.notANumber s => pure s!"Not a number: \"{s}\""
  try result catch
  | Err.divByZero => pure "Divsion by zero!"
  | Err.notANumber s => pure s!"\"{s}\""

namespace StateT

def StateT
: Type u → (Type u → Type v) → Type u → Type (max u v)
| σ, m, α => σ → m (α × σ)

instance [Monad m] : Monad (StateT σ m) where
  pure x := λ s ↦ pure (x, s)
  bind sa f := λ s ↦ do
    let (a, s') ← sa s
    let sa' := f a
    sa' s'

end StateT

structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err' where
| notALetter : Char → Err'
deriving Repr

def vowels :=
  let lowerVowels := "aeiouy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfgklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters
: String → StateT LetterCounts (Except Err') Unit
| str =>
  let rec loop
  : List Char → StateT LetterCounts (Except Err') Unit
  | [] => pure ()
  | c :: cs => do
    let st ← get
    let st' ←
      if c.isAlpha then
        if vowels.contains c then
          pure {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          pure {st with consonants := st.consonants + 1}
        else
          pure st
      else
        throw (Err'.notALetter c)
    set st'
    loop cs
  loop str.toList
def countLetters'
: String → StateT LetterCounts (Except Err') Unit
| str =>
  let rec loop
  : List Char → StateT LetterCounts (Except Err') Unit
  | [] => pure ()
  | c :: cs => do
    if c.isAlpha then
      if vowels.contains c then
        modify λ st ↦ {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify λ st ↦ {st with consonants := st.consonants + 1}
      else
        pure ()
    else
      throw (Err'.notALetter c)
    loop cs
  loop str.toList

namespace MonadState

def StateT
: Type u → (Type u → Type v) → Type u → Type (max u v)
| σ, m, α => σ → m (α × σ)

class MonadState (σ : Type u) (m : Type u → Type v) : Type (max (u + 1) v) where
  get : m σ
  set : σ → m PUnit
  modifyGet : (σ → α × σ) → m α
  modify : (σ → σ) → m PUnit := λ f ↦
    modifyGet λ s ↦ (PUnit.unit, f s)

instance [Monad m] : Monad (StateT σ m) where
  pure x := λ s ↦ pure (x, s)
  bind sa f := λ s ↦ do
    let (a, s') ← sa s
    let sa' := f a
    sa' s'

def StateT.get [Monad m]
: StateT σ m σ
:= λ s ↦ pure (s, s)
def StateT.set [Monad m]
: σ → StateT σ m PUnit
| s => λ _ ↦ pure ((), s)
def StateT.modifyGet [Monad m]
: (σ → α × σ) → StateT σ m α
| f => λ s ↦ pure (f s)
instance [Monad m] : MonadState σ (StateT σ m) where
  get := StateT.get
  set := StateT.set
  modifyGet := StateT.modifyGet

end MonadState

def modify [MonadState σ m]
: (σ → σ) → m Unit
| f => modifyGet λ s ↦ ((), f s)

end Note

namespace Exercise

-- def State
-- : Type u → Type v → Type (max u v)
-- | σ, α => σ → (α × σ)
--
-- def StateT
-- : Type u → (Type u → Type v) → Type u → Type v
-- | σ, m, α => m (State σ α)

/-! # Logging Transformer
Define a monad transformer version of `WithLog`. Also define the corresponding
type class `MonadWithLog`, and write a program that combines logging and
exceptions.
-/

structure WithLog (logged : Type u) (α : Type u) : Type u where
  log : List logged
  val : α
deriving Repr

def WithLog.pure
: α → WithLog logged α
:= WithLog.mk []
def WithLog.bind
: WithLog logged α → (α → WithLog logged β) → WithLog logged β
| ma, f =>
  let a := ma.val
  let mb := f a
  WithLog.mk (ma.log ++ mb.log) mb.val
instance : Monad (WithLog logged) where
  pure := WithLog.pure
  bind := WithLog.bind

def WithLogT
: Type u → (Type u → Type v) → Type u → Type v
| logged, m, α => m (WithLog logged α)
def WithLogT.mk : m (WithLog logged α) → WithLogT logged m α := id
def WithLogT.run : WithLogT logged m α → m (WithLog logged α) := id

def WithLogT.save [Monad m]
: logged → WithLogT logged m Unit
| log => WithLogT.mk do
  pure (WithLog.mk [log] ())

def WithLogT.pure [Monad m]
: α → WithLogT logged m α
:= WithLogT.mk ∘ Pure.pure ∘ WithLog.pure
def WithLogT.bind [Monad m]
: WithLogT logged m α → (α → WithLogT logged m β) → WithLogT logged m β
| ma, f => WithLogT.mk do
  let a ← ma
  let mb := f a.val
  let b ← mb
  Pure.pure (WithLog.mk (a.log ++ b.log) b.val)
instance [Monad m] : Monad (WithLogT logged m) where
  pure := WithLogT.pure
  bind := WithLogT.bind

def sumAndFindEvensAndErrorAt7
: List Int → WithLogT Int (Except String) Int
| [] => pure 0
| i :: is => do
  if i == 7 then
    Except.error "Your list contains at least one 7!"
  else if i % 2 == 0 then
    WithLogT.save i
  else
    pure ()
  let sumOfIs ← sumAndFindEvensAndErrorAt7 is
  pure (i + sumOfIs)
#eval (sumAndFindEvensAndErrorAt7 [1,2,3,4,5,6]).run
#eval (sumAndFindEvensAndErrorAt7 [1,2,3,4,5,6,7]).run

namespace WithLogFromState

abbrev WithLogT logged m α := StateT (List logged) m α
abbrev WithLog logged α := WithLogT logged Id α

def sumAndFindEvens
: List Int → WithLog Int Int
| [] => pure 0
| i :: is => do
  if i % 2 == 0 then
    modify (λ evens ↦ i :: evens)
  else
    pure ()
  let sumOfIs ← sumAndFindEvens is
  pure (i + sumOfIs)
#eval (sumAndFindEvens [1,2,3,4,5,6]).run []

def sumAndFindEvensAndErrorAt7
: List Int → WithLogT Int (Except String) Int
| [] => pure 0
| i :: is => do
  if i == 7 then
    Except.error "Your list contains at least one 7!"
  else if i % 2 == 0 then
    modify (λ evens ↦ i :: evens)
  else
    pure ()
  let sumOfIs ← sumAndFindEvensAndErrorAt7 is
  pure (i + sumOfIs)
#eval (sumAndFindEvensAndErrorAt7 [1,2,3,4,5,6]).run []
#eval (sumAndFindEvensAndErrorAt7 [1,2,3,4,5,6,7]).run []

end WithLogFromState

/-! # Counting Files
Modify `doug`'s monad with `StateT` such that it counts the number of
directories and files seen. At the end of execution, it should display a report
like:
```
Viewed 38 files in 5 directories.
```
-/

namespace doug_ver_4

structure Config : Type where
  useASCII : Bool := false
  currentPrefix : String := ""
  showAll : Bool := false
  startingDir : IO System.FilePath := IO.currentDir

def Config.preFile
: Config → String
| cfg =>
  if cfg.useASCII
  then "|--"
  else "├──"

def Config.preDir
: Config → String
| cfg =>
  if cfg.useASCII
  then "|  "
  else "│  "

def Config.inDirectory
: Config → Config
| cfg => {cfg with currentPrefix := s!"{cfg.preDir} {cfg.currentPrefix}"}

abbrev ConfigIO α := ReaderT Config IO α

structure Context where
  fileCount : Nat := 0
  dirCount : Nat := 0

abbrev ContextIO α := StateT Context IO α
abbrev ConfigContextIO α := ReaderT Config ContextIO α

def printFileName
: String → ConfigContextIO Unit
| fileName => do
  let cfg ← read
  monadLift <|
    IO.println s!"{cfg.currentPrefix}{cfg.preFile} {fileName}"

def printDirName
: String → ConfigContextIO Unit
| dirName => do
  let cfg ← read
  (monadLift : ContextIO Unit → ConfigContextIO Unit) <|
  (monadLift : IO Unit → ContextIO Unit) <|
    IO.println s!"{cfg.currentPrefix}{cfg.preFile} {dirName}/"

def fileCountPlusPlus
: ConfigContextIO Unit :=
  (monadLift : ContextIO Unit → ConfigContextIO Unit) <|
  modify (λ cxt ↦ {cxt with fileCount := cxt.fileCount + 1})

def dirCountPlusPlus
: ConfigContextIO Unit :=
  modify (λ cxt ↦ {cxt with dirCount := cxt.dirCount + 1})

inductive Entry : Type where
| file : String → Entry
| dir : String → Entry
def toEntry
: System.FilePath → ConfigContextIO (Option Entry)
| path =>
  match path.components.getLast? with
  | Option.none => pure ∘ Option.some ∘ Entry.dir <| ""
  | Option.some "."
  | Option.some ".." => pure Option.none
  | Option.some name => do
    if name.toList.head? == Option.some '.' && (← read).showAll == false
    then pure Option.none
    else
      pure ∘ Option.some <|
        if ← path.isDir
        then Entry.dir name
        else Entry.file name

def mapA [Applicative f]
: List α → (α → f β) → f (List β)
| [], _ => pure []
| a :: as, f =>
  let fb := f a
  let fbs := mapA as f
  pure List.cons <*> fb <*> fbs

partial def dirTree
: System.FilePath → ConfigContextIO Unit
| path => do
  match ← toEntry path with
  | Option.none => pure ()
  | Option.some (Entry.file name) =>
    printFileName name
    fileCountPlusPlus
  | Option.some (Entry.dir name) =>
    printDirName name
    dirCountPlusPlus
    let contents ← monadLift path.readDir
    withReader (·.inDirectory) (mapA contents.toList (dirTree ·.path)) *>
      pure ()

def main : List String → IO UInt32
| args => do
  match args2config? args with
  | Option.some cfg =>
    let (_, cxt) ← ((dirTree (← cfg.startingDir)).run cfg).run {}
    IO.println s!"Viewed {cxt.fileCount} files in {cxt.dirCount} directories."
    pure 0
  | Option.none =>
    IO.eprintln s!"Didn't understand argument(s) {concatWith args " "}"
    IO.eprintln usage
    pure 1
where
  args2config? : List String → Option Config
  | [] => Option.some {}
  | "--ascii" :: rest =>
    (λ cfg ↦ {cfg with useASCII := true}) <$> args2config? rest
  | "--all" :: rest =>
    (λ cfg ↦ {cfg with showAll := true}) <$> args2config? rest
  | "--target" :: pathString :: rest =>
    (λ cfg ↦ {cfg with startingDir := pure ∘ System.FilePath.mk <| pathString})
    <$> args2config? rest
  | _ => Option.none
  concatWith : List String → String → String
  | [], _ => ""
  | a :: as, b => a ++ b ++ concatWith as b
  usage : String := "\
Usage: doug [--ascii] [--all] [--target <path>]
Options:
\t--ascii\tUse ASCII characters to display the directory structure
\t--all\tShow all including filenames that begin with a dot
\t--target <path>\tSet a target <path>, or run in pwd\
"

#eval System.FilePath.mk "/home"
#eval main ["--all", "--ascii", "--target", "./Fpl/"]

end doug_ver_4

end Exercise
