import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkApp (mkConst ``Nonempty [0]) (mkConst ``False)
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 20 && ci.type == target then
      logInfo m!"nonempty false decl {n}"
      count := count + 1
