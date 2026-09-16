import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta

def printAllDecls : CoreM Unit := do
  let env ← getEnv
  for (n, _) in env.constants do
    let nameStr := n.toString
    if nameStr.containsSubstr "179524" || nameStr.containsSubstr "Sun" || nameStr.containsSubstr "sun" then
      IO.println nameStr

#eval printAllDecls
