import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (s.contains "factorial" || ns.contains "factorial") && (s.contains "choose" || ns.contains "choose" || s.contains "∣" || ns.contains "dvd") then
      if ns.startsWith "Nat." || ns.contains "factorial" || ns.contains "choose" then
        logInfo m!"{name} : {ci.type}"
