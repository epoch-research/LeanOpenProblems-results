import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "#sorry_decls_fc" : command => do
  let env ← getEnv
  let mut shown := 0
  let mut total := 0
  for (name, ci) in env.constants.toList do
    let s := toString name
    if !(s.startsWith "FormalConjectures" || s.startsWith "ProblemAttributes" || s.startsWith "Google" || s.contains "NormalNumber" || s.contains "IsEquidistributed") then continue
    try
      let axs ← Lean.collectAxioms name
      if axs.contains `sorryAx then
        total := total + 1
        if shown < 200 then
          logInfo m!"{name} : {ci.type}"
          shown := shown+1
    catch _ => pure ()
  logInfo m!"total {total}, shown {shown}"
#sorry_decls_fc
