import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.contains "prime" || ns.contains "Prime" || ns.contains "Chebyshev" || ns.contains "theta" || ns.contains "psi") &&
       (s.contains "~[" || s.contains "IsEquivalent" || s.contains "=o" || s.contains "=O" || s.contains "Tendsto" || s.contains "Filter.atTop" || s.contains "asymp" || s.contains "Asymptotics") then
      logInfo m!"{name} : {ci.type}"
