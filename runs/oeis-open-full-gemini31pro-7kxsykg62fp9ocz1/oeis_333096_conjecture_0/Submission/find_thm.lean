import Submission.Spec
import Lean

open Lean Meta

def findTheorem : MetaM Unit := do
  let env ← getEnv
  let targetType ← Meta.inferType (mkConst ``oeis_333096_conjecture_0)
  for (name, info) in env.constants.toList do
    if info.isThm then
      let ty := info.type
      if ty == targetType then
        IO.println s!"Found: {name}"

#eval findTheorem
