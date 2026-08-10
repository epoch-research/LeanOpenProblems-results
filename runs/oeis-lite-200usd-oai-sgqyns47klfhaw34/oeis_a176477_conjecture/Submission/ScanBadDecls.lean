import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let target1 := mkConst ``False
  let target2 := mkApp (mkConst ``Nonempty [0]) (mkConst ``False)
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.cleanupAnnotations
    if ty == target1 || ty == target2 then
      logInfo m!"bad-like {n} : {ty}"
      c := c + 1
  logInfo m!"count {c}"
