def List.generate (elem : α)
: (len : Nat) → List α
| 0 => []
| len + 1 => elem :: List.generate elem len

structure Env : Type where
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream
  p : Nat

structure Sta : Type where
  index : Nat

inductive Event : Type where
| join : Nat → Event
| sorting : Event
deriving Inhabited

def r (stdin : IO.FS.Stream) : IO (Nat × Nat × List Nat) := do
  let nkp ← (λ s ↦ s.split (· = ' ')) <$> String.trim <$> stdin.getLine
  let (n, k, p) :=
    match nkp with
    | [] | [_] | [_,_] => panic! "NKP is not enough!"
    | [n, k, p] =>
      match n.toNat?, k.toNat?, p.toNat? with
      | .some n, .some k, .some p => (n, k, p)
      | _, _, _ => panic! "NKP is not a nat!"
    | _ => panic! "NKP is too much"
  let ps ← List.map (λ n ↦
    match n.toNat? with
    | .some n => n
    | _ => panic! "Someone's height is not a nat!"
  ) <$> (List.generate 0 n |>.mapM (λ _ ↦ String.trim <$> stdin.getLine))
  pure (k, p, p :: ps)

def runEvent
: (k : Nat) → StateT Sta (ReaderT Env IO) Unit
| 0 => return
| k + 1 => do
  let env ← read
  let input ← (λ s ↦ s.split (· = ' ')) <$> String.trim <$> env.stdin.getLine
  let event : Event :=
    match input with
    | ["join", p'] =>
      match p'.toNat? with
      | .some p' => .join p'
      | _ => panic! "Join event received is not a nat!"
    | ["sorting"] => .sorting
    | _ => panic! "Event not satisified!"
  match event with
  | .join p' =>
    if p' < env.p
    then set {(← get) with index := (← get).index + 1}
    else if p' > env.p
    then pure ()
    else panic! "Your height of the insert-classmate is same as Mr.paiza's!"
  | .sorting =>
    env.stdout.putStrLn s!"{(← get).index + 1}"
  runEvent k

def main : IO Unit := do
  let stdin ← IO.getStdin
  -- let stdin ← IO.FS.Stream.ofHandle
  --   <$> IO.FS.Handle.mk "test.practice21.01.txt" IO.FS.Mode.read
  -- let stdin ← IO.FS.Stream.ofHandle
  --   <$> IO.FS.Handle.mk "test.practice21.02.txt" IO.FS.Mode.read
  let stdout ← IO.getStdout
  let (k, p, ps) ← r stdin
  let env : Env := ⟨stdin, stdout, p⟩
  let index :=
    match ps.mergeSort.idxOf? p with
    | .some index => index
    | _ => panic! "Your class does not have Mr.paiza!"
  let sta : Sta := ⟨index⟩
  runEvent k |>.run' sta |>.run env
