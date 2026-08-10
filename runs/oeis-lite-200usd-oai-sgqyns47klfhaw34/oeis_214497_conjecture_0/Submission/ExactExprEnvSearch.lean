import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#exact_expr_env_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      let s := toString ci.type
      if s.contains "3 ^" && s.contains "2 ^" && s.contains "Nat.Prime" then
        logInfo m!"{name} : {ci.type}"
        shown := shown + 1
    logInfo m!"shown={shown}"

#exact_expr_env_search
