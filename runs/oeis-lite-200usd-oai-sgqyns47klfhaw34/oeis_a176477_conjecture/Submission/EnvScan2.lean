import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "False" || ns.contains "false" || ns.contains "absurd" || ns.contains "impossible" || ns.contains "contrad" then
      let ts := toString ci.type
      if ts.contains "False" || ts.contains "∀" then
        logInfo m!"{n} : {ci.type}"
        count := count + 1
        if count > 300 then break
  logInfo m!"count {count}"
