import FormalConjectures.Util.ProblemImports
import Submission.Spec
open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := toString c.type
    if s.containsSubstr "a n = 0" then
      IO.println n
