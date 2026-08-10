import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

instance : LinearOrder Empty := inferInstance
instance : NoMaxOrder Empty where exists_gt := by intro a; cases a
instance : NoMinOrder Empty where exists_lt := by intro a; cases a
instance : WellFoundedLT Empty where wf := by exact ⟨fun a => by cases a⟩
instance : WellFoundedGT Empty where wf := by exact ⟨fun a => by cases a⟩
instance : DenselyOrdered Empty where dense := by intro a; cases a
#synth LinearOrder Empty
#synth NoMaxOrder Empty

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target := mkApp (mkConst ``Nonempty [levelOne]) (mkConst ``Empty)
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if ci.isUnsafe then continue
    liftTermElabM <| do
      let us := ci.levelParams.map (fun _ => levelZero)
      let ty ← inferType (mkConst n us)
      let (xs, _, body) ← forallMetaTelescopeReducing ty
      if (← isDefEq body target) then
        let e := mkAppN (mkConst n us) xs
        try synthesizeSyntheticMVarsNoPostponing catch _ => pure ()
        let e ← instantiateMVars e
        let t ← instantiateMVars (← inferType e)
        if !e.hasExprMVar && !t.hasExprMVar then
          logInfo m!"CLOSED {n} : {← ppExpr t}"
  logInfo m!"done"
