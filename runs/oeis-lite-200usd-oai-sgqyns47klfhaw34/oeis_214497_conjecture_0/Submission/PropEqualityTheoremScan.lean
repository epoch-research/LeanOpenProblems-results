import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if c < 250 && (ns.contains "prop" || ns.contains "Prop" || ns.contains "decide" || ns.contains "Decidable") then
      let s := toString ci.type
      if (s.contains "Prop" && (s.contains "=" || s.contains "↔" || s.contains "Decidable" || s.contains "Bool")) then
        c := c + 1
        logInfo m!"{n} : {ci.type}"
