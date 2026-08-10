import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.startsWith "FormalConjecturesForMathlib" then
      if ci.type.isConstOf ``False then
        IO.println s!"False decl {n}"
