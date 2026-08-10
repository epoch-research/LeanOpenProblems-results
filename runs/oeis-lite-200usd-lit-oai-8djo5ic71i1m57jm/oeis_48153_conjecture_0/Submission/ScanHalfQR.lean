import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    let s := toString info.type
    let ns := toString name
    if (s.contains "legendreSym" || s.contains "quadraticChar" || ns.contains "legendre" || ns.contains "quadratic") &&
       (s.contains "/ 2" || s.contains "Ico" || s.contains "range" || s.contains "card" || s.contains "sum") then
      logInfo m!"{name} : {info.type}"
      count := count + 1
      if count > 500 then break
