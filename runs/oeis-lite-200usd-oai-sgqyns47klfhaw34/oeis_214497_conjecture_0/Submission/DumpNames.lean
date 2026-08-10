import FormalConjectures.Util.ProblemImports
open Lean Meta
unsafe def dumpNames : CoreM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    logInfo m!"NAME {n} : {ci.type}"
#eval! dumpNames
