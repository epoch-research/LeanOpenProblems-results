import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 8000000
open Lean Meta Elab Command

elab "#scan_closed_contradict_norm" : command => do
  liftTermElabM do
    let env ← getEnv
    let posRef ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap String Name)
    let negRef ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap String Name)
    let printedRef ← IO.mkRef (0 : Nat)
    for (n, ci) in env.constants.toList do
      if (← printedRef.get) > 50 then return ()
      try
        forallTelescope ci.type fun xs body => do
          unless xs.size == 0 do return ()
          let body ← instantiateMVars body
          let key ← do
            let b ← reduce body
            pure (toString (← ppExpr b))
          if body.isAppOfArity ``Not 1 then
            let p ← reduce body.appArg!
            let k := toString (← ppExpr p)
            let pos ← posRef.get
            match pos.get? k with
            | some pn =>
                printedRef.modify (· + 1)
                logInfo m!"PAIR: {pn} and neg {n}\n  {p}"
            | none => negRef.modify (·.insert k n)
          else
            let neg ← negRef.get
            match neg.get? key with
            | some nn =>
                printedRef.modify (· + 1)
                logInfo m!"PAIR: pos {n} and neg {nn}\n  {body}"
            | none => posRef.modify (·.insert key n)
      catch _ => pure ()

#scan_closed_contradict_norm
