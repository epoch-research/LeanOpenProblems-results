import Submission.test_answer
import Lean

open Lean

def checkVal : CoreM Unit := do
  let env ← getEnv
  match env.find? `my_proof with
  | some (.thmInfo val) =>
    IO.println s!"Type: {← Meta.MetaM.run' (Meta.ppExpr val.type)}"
    IO.println s!"Value: {← Meta.MetaM.run' (Meta.ppExpr val.value)}"
    IO.println s!"Contains sorryAx: {val.value.hasSorry}"
  | _ => IO.println "Not found"

#eval! checkVal
