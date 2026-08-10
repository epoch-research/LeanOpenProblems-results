import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.contains "choose" || s.contains "choose") && (ns.contains "dvd" || s.contains "∣" || s.contains "Coprime" || s.contains "gcd") then
      if ns.startsWith "Nat." || ns.contains "choose" then
        logInfo m!"{name} : {ci.type}"
