import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def hasForallPropToBVar0 : Expr → Bool
| .forallE _ d b _ => d.isSort && hasForallPropToBVar0 b
| .bvar 0 => true
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 20 && hasForallPropToBVar0 ci.type then
      logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
