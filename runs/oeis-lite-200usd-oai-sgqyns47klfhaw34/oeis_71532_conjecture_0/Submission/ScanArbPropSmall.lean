import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 5000000
open Lean Meta Elab Command

elab "#scan_arb_prop_small" : command => do
  liftTermElabM do
    let env ← getEnv
    let countRef ← IO.mkRef (0 : Nat)
    for (n, ci) in env.constants.toList do
      if (← countRef.get) > 300 then return ()
      forallTelescope ci.type fun xs body => do
        if xs.size > 6 then return ()
        if body.isFVar then
          let d ← body.fvarId!.getDecl
          let k ← whnf d.type
          if k.isSort then
            -- skip obvious noConfusion by name
            let ns := n.toString
            unless ns.contains "noConfusion" do
              countRef.modify (· + 1)
              logInfo m!"ARB_SMALL {n} nargs={xs.size}\n  {ci.type}"

#scan_arb_prop_small
