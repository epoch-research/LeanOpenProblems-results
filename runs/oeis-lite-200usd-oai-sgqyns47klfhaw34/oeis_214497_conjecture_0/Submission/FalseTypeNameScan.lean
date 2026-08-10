import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "False" && !(toString n).contains "_proof_" && c < 300 then
      c := c + 1
      logInfo m!"{n} : {ci.type}"
  logInfo m!"count shown {c}"
