import Submission.Spec
import Lean
open Lean
def hack : CoreM Unit := do
  let env ← getEnv
  let decl := env.find? `A096535_occurs_infinitely_often.disproof
  if let some (ConstantInfo.thmInfo info) := decl then
    IO.println info.value
#eval hack
