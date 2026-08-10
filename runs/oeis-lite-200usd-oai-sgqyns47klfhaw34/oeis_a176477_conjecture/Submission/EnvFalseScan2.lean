import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let falseName := ``False
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.consumeMData
    if ty.isConstOf falseName then
      logInfo m!"{n} : {ty}"
      cnt := cnt + 1
  logInfo m!"false count {cnt}"
