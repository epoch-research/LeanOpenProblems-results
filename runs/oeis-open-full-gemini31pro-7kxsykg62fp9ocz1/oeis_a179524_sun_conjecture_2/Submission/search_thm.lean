import Submission.Spec
import Lean

open Lean Meta

def checkType (type : Expr) : CoreM Bool := do
  return (toString type).containsSubstr "legendreSym"

def printMatchingDecls : CoreM Unit := do
  let env ← getEnv
  for (n, c) in env.constants do
    let nameStr := n.toString
    if nameStr.startsWith "Mathlib" || nameStr.startsWith "Lean" || nameStr.startsWith "Std" || nameStr.startsWith "Init" then
      continue
    let typeStr := toString c.type
    if typeStr.containsSubstr "20 *" then
      IO.println n.toString

#eval printMatchingDecls
