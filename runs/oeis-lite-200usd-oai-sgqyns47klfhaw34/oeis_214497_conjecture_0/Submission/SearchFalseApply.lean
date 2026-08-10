import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

-- Try applying every theorem whose result (after whnf/forall intro) is False, letting typeclasses synthesize.
elab "#search_false_apply" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut hits := #[]
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let ty := ci.type
      -- quick textual filter
      if !(toString ty).contains "False" then continue
      try
        let c := mkConst name (ci.levelParams.map mkLevelParam)
        -- Create metavars for all explicit/implicit args by repeated forallTelescopeReducing.
        forallTelescopeReducing ty fun xs body => do
          let body ← instantiateMVars body
          if body.isConstOf ``False then
            let app := mkAppN c xs
            let (_, mvars) ← forallTelescopeReducing ty fun xs body => pure (mkAppN c xs, #[])
            -- skip: this doesn't synthesize; just record closed arity names maybe
            if xs.isEmpty then hits := hits.push name
      catch _ => pure ()
    logInfo m!"closed False-like hits: {hits}"

#search_false_apply
