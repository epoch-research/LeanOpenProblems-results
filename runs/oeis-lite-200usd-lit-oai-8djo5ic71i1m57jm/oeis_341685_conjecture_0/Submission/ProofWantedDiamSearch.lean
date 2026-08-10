import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show MetaM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.toString.contains "diam_ne_zero" then
      let fmt ← ppExpr ci.type
      let axs ← Lean.collectAxioms n
      logInfo m!"{n} : {fmt} | axioms {axs}"
