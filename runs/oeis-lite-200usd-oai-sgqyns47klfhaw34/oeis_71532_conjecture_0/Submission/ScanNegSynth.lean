import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 3000000
open Lean Meta Elab Command

elab "#scan_neg_synth" : command => do
  liftTermElabM do
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      let ty := ci.type
      forallTelescope ty fun xs body => do
        unless xs.size == 0 do return ()
        if body.isAppOfArity ``Not 1 then
          let p := body.appArg!
          try
            let inst ← synthInstance p
            logInfo m!"SYNTH_POS_FOR_NEG {n}\n  P={p}\n  inst={inst}"
          catch _ => pure ()
#scan_neg_synth
