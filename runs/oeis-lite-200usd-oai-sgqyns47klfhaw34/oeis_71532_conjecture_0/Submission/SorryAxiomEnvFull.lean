import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "#sorry_decls_full" : command => do
  let env ← getEnv
  let mut shown := 0
  let mut total := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    try
      let axs ← Lean.collectAxioms name
      if axs.contains `sorryAx then
        total := total + 1
        if shown < 200 then
          logInfo m!"{name} : {ci.type}"
          shown := shown+1
    catch _ => pure ()
  logInfo m!"total {total}, shown {shown}"
#sorry_decls_full
