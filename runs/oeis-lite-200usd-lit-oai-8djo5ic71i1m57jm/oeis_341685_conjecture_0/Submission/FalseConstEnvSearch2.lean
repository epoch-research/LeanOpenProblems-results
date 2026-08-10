import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show CoreM Unit from do
  let env ← getEnv
  let falseExpr := mkConst ``False
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if ci.type == falseExpr then
      count := count + 1
      IO.println s!"FALSE CONST {n}"
  IO.println s!"false count {count}"
