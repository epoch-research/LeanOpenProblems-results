import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "Nat.Prime" && s.contains "3 ^" && s.contains "2 ^" then
      logInfo m!"{name} : {ci.type}"
      count := count + 1
  logInfo m!"count={count}"
