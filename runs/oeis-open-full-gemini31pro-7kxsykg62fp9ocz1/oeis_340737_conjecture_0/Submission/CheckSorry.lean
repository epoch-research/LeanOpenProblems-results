import Lean

open Lean

def checkSorry (declName : Name) : CoreM Unit := do
  let env ← getEnv
  match env.find? declName with
  | some decl =>
    let val := decl.value!
    if val.hasSorry then
      IO.println "Has sorry"
    else
      IO.println "No sorry"
  | none => IO.println "Not found"
