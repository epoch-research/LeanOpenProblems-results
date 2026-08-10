import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#check (inferInstance : Fact (Nat.Prime 2))
-- expected failures if uncommented:
-- #check (inferInstance : Fact (Nat.Prime 0))
-- #check (inferInstance : Fact (Nat.Prime 1))
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if s.contains "Fact" && s.contains "Nat.Prime" then
      count := count + 1
      if count ≤ 200 then logInfo m!"{name} : {ci.type}"
  logInfo m!"total {count}"
