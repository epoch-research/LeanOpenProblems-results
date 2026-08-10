import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["Nat.Prime 0", "Nat.Prime 1", "Nat.Prime 4", "Nat.Prime 6", "Nat.Prime 8", "Nat.Prime 9", "Nat.Prime 10", "Prime 0", "Prime 1"]
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if needles.any (fun nd => s.contains nd) then
      count := count + 1
      if shown < 200 then
        logInfo m!"{name} : {ci.type}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
