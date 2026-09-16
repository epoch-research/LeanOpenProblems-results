import Submission.Spec
import Lean

open Lean Meta

def dumpEnv : CoreM Unit := do
  let env ← getEnv
  for (n, c) in env.constants do
    let nameStr := n.toString
    if nameStr.startsWith "FormalConjectures" then
      IO.println s!"{n}"

#eval dumpEnv
