import FormalConjectures.Util.ProblemImports

open Lean

def printDecls : CoreM Unit := do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.containsSubstr "prime" then
      IO.println name

#eval printDecls
