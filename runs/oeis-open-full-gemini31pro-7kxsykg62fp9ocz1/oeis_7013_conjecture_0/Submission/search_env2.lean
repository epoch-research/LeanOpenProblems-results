import FormalConjectures.Util.ProblemImports
import Submission.Spec
import Lean

open Lean Meta

def searchEnv : MetaM Unit := do
  let env ← getEnv
  let mut found := #[]
  for (name, _) in env.constants do
    let nameStr := name.toString
    if nameStr.containsSubstr "oeis_7013_conjecture_0" then
      found := found.push nameStr
  IO.println s!"Found: {found}"

#eval searchEnv
