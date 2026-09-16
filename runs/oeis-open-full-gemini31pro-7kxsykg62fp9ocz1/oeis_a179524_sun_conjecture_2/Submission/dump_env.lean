import Submission.Spec
import Lean

open Lean Meta

def dumpEnv : CoreM Unit := do
  let env ← getEnv
  for (n, c) in env.constants do
    let nameStr := n.toString
    if nameStr.startsWith "Mathlib" || nameStr.startsWith "Lean" || nameStr.startsWith "Std" || nameStr.startsWith "Init" then
      continue
    let typeStr := toString c.type
    if typeStr.containsSubstr "legendreSym" || typeStr.containsSubstr "20" || typeStr.containsSubstr "sum" then
      IO.println s!"{n} : {typeStr}"

#eval dumpEnv
