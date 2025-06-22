/-
Extend `feline` with support for usage infomation. The extended version should
accept a command-line argument --help that causes documentation about the
available command-line options to be written to standard output.
-/

def bufsize : USize := 20 * 1024

partial def dump : IO.FS.Stream → IO Unit
| stream => do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else do
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

def fileStream : System.FilePath → IO (Option IO.FS.Stream)
| filename => do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure Option.none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure ∘ Option.some ∘ IO.FS.Stream.ofHandle <| handle

def process : UInt32 → List String → IO UInt32
| exitCode, [] => pure exitCode
| exitCode, "-" :: args => do
  let stdin ← IO.getStdin
  dump stdin
  process exitCode args
| exitCode, filename :: args => do
  let stream ← fileStream ∘ System.FilePath.mk <| filename
  match stream with
  | Option.none => process 1 args
  | Option.some stream =>
    dump stream
    process exitCode args

def main : List String → IO UInt32
| [] => process 0 ["-"]
| "help" :: _ => process 0 ["help.txt"]
| args => process 0 args

example (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

theorem one_eq_succ_zero : 1 = Nat.succ 0 := by
  rfl

theorem two_eq_succ_one : 2 = Nat.succ 1 := by
  rw [one_eq_succ_zero]

example : 2 = Nat.succ (Nat.succ 0) := by
  rw [two_eq_succ_one]

example : 2 = Nat.succ (Nat.succ 0) := by
  rw [← two_eq_succ_one]
