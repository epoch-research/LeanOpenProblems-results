import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if (ns.contains "legendre" || ns.contains "quadraticChar" || ns.contains "jacobiSym" || ns.contains "Gauss" || ns.contains "gauss") && (ns.contains "sum" || ns.contains "card" || ns.contains "Sum" || ns.contains "Card") then
      logInfo m!"{n} : {ci.type}"
