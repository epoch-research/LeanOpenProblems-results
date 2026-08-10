import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let patterns ← liftTermElabM do
    let P ← mkFreshExprMVar (mkSort levelZero)
    pure #[← mkForallFVars #[P] P]
  let env ← getEnv
  let mut found := 0
  for (n, ci) in env.constants.toList do
    let b ← liftTermElabM <| Meta.isDefEq ci.type patterns[0]!
    if b then
      logInfo m!"explosive: {n}"
      found := found + 1
  logInfo m!"found {found}"
