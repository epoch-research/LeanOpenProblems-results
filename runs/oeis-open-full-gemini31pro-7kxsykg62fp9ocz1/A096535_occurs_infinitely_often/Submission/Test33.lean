import Submission.Test32
import Lean

open Lean Elab Command Term

def myElab : CommandElabM Unit := do
  let env ← getEnv
  let decl1 := env.find? `A096535_occurs_infinitely_often.disproof
  let decl2 := env.find? `my_disproof
  if let (some (ConstantInfo.thmInfo info1), some (ConstantInfo.thmInfo info2)) := (decl1, decl2) then
    IO.println (info1.type == info2.type)
  else
    IO.println "Not found"

#eval myElab
