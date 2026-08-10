import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show MetaM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.toString.contains "avoids_isAPOfLength_three" then
      let fmt ← ppExpr ci.type
      logInfo m!"toString: {n}\nrepr: {repr n}\ntype: {fmt}"
