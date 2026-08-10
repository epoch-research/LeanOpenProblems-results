import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "#scan_sorryax" : command => unsafe do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 50 then
      let axs ← liftCoreM <| collectAxioms n
      if axs.contains ``sorryAx then
        logWarning m!"S {n} : {ci.type}"
        count := count + 1
  logWarning m!"count {count}"
#scan_sorryax
