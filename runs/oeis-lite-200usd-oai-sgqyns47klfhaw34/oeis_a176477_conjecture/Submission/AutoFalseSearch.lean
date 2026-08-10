import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
open Lean.Elab.Term
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ref ← IO.mkRef (#[] : Array Name)
  for (n, ci) in env.constants.toList do
    if (← ref.get).size < 20 then
      try
        MetaM.run' do
          let type ← instantiateMVars ci.type
          forallTelescopeReducing type fun xs body => do
            if body.isConstOf ``False then
              synthesizeSyntheticMVarsNoPostponing
              let xs' ← xs.mapM instantiateMVars
              let still := xs'.any (·.hasExprMVar)
              let b ← instantiateMVars body
              if !still && b.isConstOf ``False then
                ref.modify (·.push n)
      catch _ => pure ()
  logInfo m!"found {← ref.get}"
