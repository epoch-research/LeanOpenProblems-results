import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if c > 200 then pure () else
    let s := toString ci.type
    if s.contains "Nat.Prime" && (s.contains "+ 2" || s.contains "- 2" || s.contains "+ 1" || s.contains "- 1") then
      c := c + 1
      logInfo m!"{n} : {ci.type}"
