import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta

def searchEnv : MetaM Unit := do
  let env ← getEnv
  let mut found := #[]
  for (name, _) in env.constants do
    let nameStr := name.toString
    if nameStr.containsSubstr "CatalanMersenne" || nameStr.containsSubstr "oeis" || nameStr.containsSubstr "7013" then
      found := found.push nameStr
  IO.println s!"Found: {found}"

#eval searchEnv
