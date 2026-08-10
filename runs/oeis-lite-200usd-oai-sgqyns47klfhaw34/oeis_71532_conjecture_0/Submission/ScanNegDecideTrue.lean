import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 5000000
open Lean Meta Elab Command

elab "#scan_neg_decide_true" : command => do
  liftTermElabM do
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      let ty := ci.type
      forallTelescope ty fun xs body => do
        unless xs.size == 0 do return ()
        if body.isAppOfArity ``Not 1 then
          let p := body.appArg!
          try
            let decTy ← mkAppM ``Decidable #[p]
            let _ ← synthInstance decTy
            let d ← mkAppM ``decide #[p]
            let dv ← whnf d
            if dv.isConstOf ``true then
              logInfo m!"NEG_BUT_DECIDES_TRUE {n}\n  P={p}"
          catch _ => pure ()
#scan_neg_decide_true
