import FormalConjectures.Util.ProblemImports

open Lean

def printDecls : CoreM Unit := do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.containsSubstr "prime_gap" || name.toString.containsSubstr "PrimeGap" then
      IO.println name

#eval printDecls
