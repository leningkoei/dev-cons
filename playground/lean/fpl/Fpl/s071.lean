namespace doug_ver_1

structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""

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
| cfg => ⟨cfg.useASCII, s!"{cfg.preDir} {cfg.currentPrefix}"⟩
#eval (Config.mk false "").inDirectory.inDirectory.currentPrefix

def Config.fileName
: Config → String → String
| cfg, fileName => s!"{cfg.currentPrefix}{cfg.preFile} {fileName}"

def Config.dirName
: Config → String → String
| cfg, dirName => s!"{cfg.currentPrefix}{cfg.preFile} {dirName}/"

def usage : String := "\
Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure\
"

/-- # Config from Args
Try to build a config from a list of string which string should be the standard
args received from terminal.
If args is not servived, it will return a default config warped by
`Option.some`.
If args is invalid, it will return `Option.none`.
-/
def configFromArgs
: List String → Option Config
| [] => Option.some {} -- both fields default
| ["--ascii"] => Option.some { useASCII := true }
| _ => Option.none

inductive Entry where
| file : String → Entry
| dir : String → Entry

def toEntry
: System.FilePath → IO (Option Entry)
| path => do
  match path.components.getLast? with
  | none => pure ∘ some ∘ .dir <| ""
  | some "."
  | some ".." => pure none
  | some name => pure ∘ some <| if (← path.isDir) then .dir name else .file name

#eval (System.FilePath.mk "").components.getLast?

def showFileName
: Config → String → IO Unit
| cfg, fileName =>
  IO.println (cfg.fileName fileName)

def showDirName
: Config → String → IO Unit
| cfg, dirName =>
  IO.println (cfg.dirName dirName)

def doList [Applicative f]
: List α → (α → f Unit) → f Unit
| [], _ => pure ()
| a :: as, f => f a *> doList as f

partial def dirTree
: Config → System.FilePath → IO Unit
| cfg, path => do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName cfg name
  | some (.dir name) =>
    showDirName cfg name
    let contents ← path.readDir
    let newConfig := cfg.inDirectory
    doList contents.toList (λ d ↦ dirTree newConfig d.path)

def concatWith
: List String → String → String
| [], _ => ""
| a :: as, x => a ++ x ++ concatWith as x

def main
: List String → IO UInt32
| args => do
  match configFromArgs args with
  | Option.some config =>
    dirTree config (← IO.currentDir)
    pure 0
  | Option.none =>
    IO.eprintln s!"Didn't understand argument(s) {concatWith args " "}\n"
    IO.eprintln usage
    pure 1

#eval IO.println "Hello, world!"
#eval main []

end doug_ver_1

namespace doug_ver_2

structure Config : Type where
  useASCII : Bool
  currentPrefix : String

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
  then "|--"
  else "│  "

def Config.showFileName
: Config → String → String
| cfg, fileName => s!"{cfg.currentPrefix}{cfg.preFile} {fileName}"

def Config.showDirName
: Config → String → String
| cfg, name => s!"{cfg.currentPrefix}{cfg.preFile} {name}/"

def Config.inDirectory
: Config → Config
| cfg => Config.mk cfg.useASCII s!"{cfg.preDir} {cfg.currentPrefix}"

def ConfigIO : Type → Type
| α => Config → IO α

def ConfigIO.run
: ConfigIO α → Config → IO α
| action, cfg => action cfg

def ConfigIO.ask
: ConfigIO Config
:= λ cfg ↦ pure cfg

def ConfigIO.local
: (Config → Config) → ConfigIO α → ConfigIO α
| change, action => λ cfg ↦ action (change cfg)

def ConfigIO.runIO
: IO α → ConfigIO α
| action => λ _cfg ↦ action

instance : Monad ConfigIO where
  pure a := λ _cfg ↦ pure a
  bind ma f := λ cfg ↦ do
    let a ← ma cfg
    let mb := f a
    let b ← mb cfg
    pure b

def printFileName
: String → ConfigIO Unit
| fileName => do
  let cfg ← ConfigIO.ask
  let showedFileName := cfg.showFileName fileName
  ConfigIO.runIO ∘ IO.println <| showedFileName

def printDirName
: String → ConfigIO Unit
| name => do
  let cfg ← ConfigIO.ask
  let showedDirName := cfg.showDirName name
  ConfigIO.runIO ∘ IO.println <| showedDirName

def usage : String := "\
Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure\
"

def configFromArgs
: List String → Option Config
| [] => Option.some <| Config.mk Bool.false ""
| ["--ascii"] => Option.some <| Config.mk Bool.true ""
| _ => Option.none

inductive Entry : Type where
| file : String → Entry
| dir : String → Entry
def toEntry
: System.FilePath → IO (Option Entry)
| path =>
  match path.components.getLast? with
  | Option.none => pure ∘ Option.some ∘ Entry.dir <| ""
  | Option.some "."
  | Option.some ".." => pure Option.none
  | Option.some name => do pure ∘ Option.some <|
    if ← path.isDir
    then Entry.dir <| name
    else Entry.file <| name

def mapA [Applicative f]
: List α → (α → f β) → f (List β)
| [], _ => pure []
| a :: as, f =>
  let fb := f a
  let fbs := mapA as f
  pure (λ b bs ↦ b :: bs) <*> fb <*> fbs

partial def dirTree
: System.FilePath → ConfigIO Unit
| path => do
  match ← ConfigIO.runIO (toEntry path) with
  | Option.none => pure ()
  | Option.some (Entry.file name) => printFileName name
  | Option.some (Entry.dir name) =>
    printDirName name
    let contents ← ConfigIO.runIO path.readDir
    ConfigIO.local (·.inDirectory) (mapA contents.toList f) *> pure ()
where
  f : IO.FS.DirEntry → ConfigIO Unit
  | d => dirTree d.path

def concatWith
: List String → String → String
| [], _ => ""
| a :: as, x => a ++ x ++ concatWith as x

def main
: List String → IO UInt32
| args => do
  match configFromArgs args with
  | Option.some cfg =>
    (dirTree (← IO.currentDir)).run cfg
    pure 0
  | Option.none =>
    IO.eprintln s!"Didn't understand argument(s) {concatWith args " "}"
    IO.eprintln usage
    pure 1

#eval main []

end doug_ver_2

namespace doug_ver_3

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

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

def printFileName
: String → ConfigIO Unit
| fileName => do
  let cfg ← read
  monadLift <|
    IO.println s!"{cfg.currentPrefix}{cfg.preFile} {fileName}"

def printDirName
: String → ConfigIO Unit
| dirName => do
  let cfg ← read
  monadLift <|
    IO.println s!"{cfg.currentPrefix}{cfg.preFile} {dirName}/"

inductive Entry : Type where
| file : String → Entry
| dir : String → Entry
def toEntry
: System.FilePath → ConfigIO (Option Entry)
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
: System.FilePath → ConfigIO Unit
| path => do
  match ← toEntry path with
  | Option.none => pure ()
  | Option.some (Entry.file name) => printFileName name
  | Option.some (Entry.dir name) =>
    printDirName name
    let contents ← monadLift path.readDir
    withReader (·.inDirectory) (mapA contents.toList (dirTree ·.path)) *>
      pure ()

def main : List String → IO UInt32
| args => do
  match args2config? args with
  | Option.some cfg =>
    (dirTree (← cfg.startingDir)).run cfg
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
#eval main ["--all", "--ascii", "--target", "./Fpl/Data"]

end doug_ver_3
