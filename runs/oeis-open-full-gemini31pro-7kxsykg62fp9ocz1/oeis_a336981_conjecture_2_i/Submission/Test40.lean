import Submission.Spec
import Lean

open Lean Meta Elab Command

elab "find_thm" : command => do
  let env ← getEnv
  let mut found := false
  for (n, c) in env.constants do
    if let ConstantInfo.thmInfo t := c then
      let nameStr := toString n
      if nameStr.containsSubstr "a336981" || nameStr.containsSubstr "336981" || nameStr.containsSubstr "sun" then
        if nameStr.containsSubstr "conjecture" then
          logInfo m!"Found thm: {n}"
  logInfo "Done."

find_thm
