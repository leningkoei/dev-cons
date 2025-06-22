/-
Step through the execution of the following program on a piece of paper:
```
def main : IO : Unit : do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
```
While stepping through the program's exection, identify when an expression is
being evaluated and when an `IO` action is being executed. When executing an
`IO` action results in a side effect, write it down. After doing this, run the
program with Lean and double-check that your predictions about side effects were
correct.
-/

def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting

#eval main

 def main' : IO Unit := do
  ((λ englishGreeting => do
    IO.println "Bonjour!"
    englishGreeting)
    (IO.println "Hello!"))

#eval main'
