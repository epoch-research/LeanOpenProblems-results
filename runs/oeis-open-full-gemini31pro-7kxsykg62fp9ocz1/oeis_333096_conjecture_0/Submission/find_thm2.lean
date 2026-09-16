import Submission.Spec
import Lean

open Lean Meta

def findTheorem : MetaM Unit := do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if info.isThm then
      let ty := info.type
      if ty.isForall then
        -- just checking if the name contains something suspicious
        if name.toString.contains "333096" then
          IO.println s!"Found: {name}"

#eval findTheorem
