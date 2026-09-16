import FormalConjectures.Util.ProblemImports
import FormalConjecturesForMathlib.NumberTheory.PrimeGap

open Lean

def printDecls : CoreM Unit := do
  let env ← getEnv
  for (name, _) in env.constants do
    if name.toString.containsSubstr "twin" || name.toString.containsSubstr "PrimeGap" then
      IO.println name

#eval printDecls
