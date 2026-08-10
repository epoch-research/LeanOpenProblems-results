import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show MetaM Unit from do
  let env ← getEnv
  let falseExpr := mkConst ``False
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if (← isDefEq ci.type falseExpr) then
      count := count + 1
      IO.println s!"FALSE CONST {n} : {ci.type}"
  IO.println s!"false count {count}"
