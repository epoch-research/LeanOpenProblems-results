import FormalConjectures.Util.ProblemImports
import Submission.Spec
open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    if c.type.isAppOf `Set.Finite then
      IO.println n
