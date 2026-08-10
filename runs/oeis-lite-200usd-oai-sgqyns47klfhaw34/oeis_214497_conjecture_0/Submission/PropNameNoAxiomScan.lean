import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    let ns := toString name
    if ns.contains "prop" || ns.contains "Prop" || ns.contains "proof_irrel" || ns.contains "propext" || ns.contains "subsingleton" || ns.contains "Subsingleton" then
      if found < 300 then logInfo m!"PNAME {name} : {ci.type}"
      found := found + 1
  logInfo m!"found {found}"
