import Submission.Spec
import Lean

open Lean Meta

def dumpEnv : CoreM Unit := do
  let env ← getEnv
  for (n, c) in env.constants do
    let nameStr := n.toString
    if nameStr.startsWith "Mathlib" || nameStr.startsWith "Lean" || nameStr.startsWith "Std" || nameStr.startsWith "Init" || nameStr.startsWith "Cli" || nameStr.startsWith "Qq" || nameStr.startsWith "Batteries" || nameStr.startsWith "Aesop" || nameStr.startsWith "ProofWidgets" then
      continue
    IO.println s!"{n}"

#eval dumpEnv
