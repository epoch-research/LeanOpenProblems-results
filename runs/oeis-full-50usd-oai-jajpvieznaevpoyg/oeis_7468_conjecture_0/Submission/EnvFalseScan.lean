import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

elab "#scan_false_theorems" : command => do
  let env ← getEnv
  let mut found := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t == mkConst ``False then
      found := found.push n
  logInfo m!"found {found.size}: {found.extract 0 (min found.size 100)}"

#scan_false_theorems
