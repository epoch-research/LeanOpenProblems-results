import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let propSort := Expr.sort .zero
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    forallTelescopeReducing ci.type fun xs body => do
      if xs.size == 1 && (← isDefEq (← inferType xs[0]!) propSort) && (← isDefEq body xs[0]!) then
        logInfo m!"arb decl {n} : {ci.type}"
        count := count + 1
  logInfo m!"count {count}"
