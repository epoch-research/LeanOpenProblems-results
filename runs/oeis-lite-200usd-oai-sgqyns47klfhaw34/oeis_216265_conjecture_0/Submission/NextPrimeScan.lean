import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.contains "next" || ns.contains "least" || ns.contains "find" || ns.contains "sInf" || ns.contains "nth") && s.contains "Nat.Prime" then
      if !(ns.contains "Polynomial" || ns.contains "Ideal" || ns.contains "Padic") then
        logInfo m!"{name} : {ci.type}"
