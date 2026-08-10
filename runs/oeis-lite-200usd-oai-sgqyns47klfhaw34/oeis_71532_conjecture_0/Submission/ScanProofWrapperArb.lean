import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 6000000
open Lean Meta Elab Command

elab "#scan_proof_wrapper_arb" : command => do
  liftTermElabM do
    let env ← getEnv
    let countRef ← IO.mkRef (0 : Nat)
    for (n, ci) in env.constants.toList do
      if (← countRef.get) > 300 then return ()
      forallTelescope ci.type fun xs body => do
        let fn := body.getAppFn
        let args := body.getAppArgs
        let mut hit := false
        if body.isAppOfArity ``Nonempty 1 then hit := true
        if body.isAppOfArity ``Inhabited 1 then hit := true
        if body.isAppOfArity ``Fact 1 then hit := true
        if body.isAppOfArity ``Decidable 1 then hit := true
        if hit then
          let p := body.appArg!
          if p.isFVar then
            let d ← p.fvarId!.getDecl
            let k ← whnf d.type
            if k.isSort then
              countRef.modify (· + 1)
              logInfo m!"WRAP_ARB {n} nargs={xs.size}\n  {ci.type}"

#scan_proof_wrapper_arb
