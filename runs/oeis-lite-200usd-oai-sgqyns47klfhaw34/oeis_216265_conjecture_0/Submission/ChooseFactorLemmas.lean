import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.contains "choose" || s.contains "choose") && (s.contains "factorization" || s.contains "factorial" || s.contains "∣" || s.contains "dvd" || s.contains "padic" || s.contains "emultiplicity") then
      logInfo m!"{name} : {ci.type}"
