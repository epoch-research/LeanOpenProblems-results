import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    if ty.isConstOf ``False then
      logInfo m!"false decl {n} : {ty}"
      count := count + 1
  logInfo m!"count {count}"
