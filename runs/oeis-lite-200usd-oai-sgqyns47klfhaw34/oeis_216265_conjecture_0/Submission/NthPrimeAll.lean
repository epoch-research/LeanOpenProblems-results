import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.contains "nth" || s.contains "nth Nat.Prime" || s.contains "Nat.nth Nat.Prime") && (s.contains "Nat.Prime" || ns.startsWith "Nat.") then
      logInfo m!"{name} : {ci.type}"
