import Submission.Spec
import Lean

open Lean Meta Elab Command

elab "find_thm2" : command => do
  let env ← getEnv
  for (n, c) in env.constants do
    let nameStr := toString n
    if nameStr.containsSubstr "5390" then
      logInfo m!"Found something: {n}"
  logInfo "Done."

find_thm2
