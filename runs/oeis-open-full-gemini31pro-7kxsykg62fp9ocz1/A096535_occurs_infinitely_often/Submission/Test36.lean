import Submission.Test35
import Lean

open Lean Elab Command Term

def myElab : CommandElabM Unit := do
  let env ← getEnv
  let decl := env.find? `A096535_occurs_infinitely_often_proof
  if let some (ConstantInfo.thmInfo info) := decl then
    IO.println (toString info.type)
  else
    IO.println "Not found"

#eval myElab
