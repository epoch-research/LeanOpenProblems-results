import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000
open Lean Meta Elab Command

elab "#scan_false_low" : command => do
  liftTermElabM do
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      if n.toString.startsWith "_" then continue
      let ty := ci.type
      try
        forallTelescopeReducing ty fun xs body => do
          let body ← whnf body
          if body.isConstOf ``False && xs.size <= 5 then
            logInfo m!"FALSE_LOW {n} nargs={xs.size}\n  {ty}"
      catch _ => pure ()

#scan_false_low
