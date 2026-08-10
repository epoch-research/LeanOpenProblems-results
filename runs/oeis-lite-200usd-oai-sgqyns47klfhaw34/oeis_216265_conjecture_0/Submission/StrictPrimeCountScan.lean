import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    let s := toString ci.type
    if (s.contains "primeCounting" || s.contains "Nat.count") && (s.contains "StrictMono" || s.contains "<" || s.contains "lt" || ns.contains "strict" || ns.contains "Strict") then
      logInfo m!"{n} : {ci.type}"
      c := c + 1
      if c > 300 then break
  logInfo m!"count {c}"
