import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
elab "#lc_deps" : command => do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    try
      let axs ← collectAxioms name
      if axs.contains `lcProof then
        shown := shown+1
        logInfo m!"{name} safety? : {ci.type}"
        if shown > 100 then break
    catch _ => pure ()
  logInfo m!"shown {shown}"
#lc_deps
