import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkApp (mkConst ``Nonempty [levelZero]) (mkConst ``Empty)
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if ci.isUnsafe then continue
    try
      liftTermElabM <| forallTelescopeReducing ci.type fun xs body => do
        if !(body.hasLooseBVars) then
          if (← isDefEq body target) then
            let e := mkAppN (mkConst n (ci.levelParams.map Level.param)) xs
            try
              synthesizeSyntheticMVarsNoPostponing
              let t ← instantiateMVars (← inferType e)
              if !t.hasExprMVar then
                logInfo m!"candidate {n} : {← ppExpr ci.type}"
                count := count+1
            catch _ => pure ()
    catch _ => pure ()
  logInfo m!"done {count}"
