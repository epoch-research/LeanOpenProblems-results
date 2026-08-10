import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "GlobalAttributeIn" || ns.contains "Translate.ToDual" || ns.contains "Tactic.Linter" || ns.contains "PGame.Algebra" || ns.contains "FiniteAbelian" then
      IO.println s!"{n} : {ci.type}"
