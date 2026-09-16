import FormalConjectures.Util.ProblemImports

open Lean Meta

def findA232194 : MetaM Unit := do
  let env ← getEnv
  for (n, _) in env.constants do
    if n.toString.containsSubstr "A232194" then
      IO.println n.toString

#eval findA232194
