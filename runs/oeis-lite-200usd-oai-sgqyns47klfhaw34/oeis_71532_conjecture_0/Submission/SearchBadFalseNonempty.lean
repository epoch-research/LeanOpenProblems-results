import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term

abbrev BadFalse := {p : False // True}
instance : LT BadFalse := ⟨fun _ _ => True⟩
instance : NoMaxOrder BadFalse where exists_gt := by intro a; exact ⟨a, trivial⟩
instance : NoMinOrder BadFalse where exists_lt := by intro a; exact ⟨a, trivial⟩
instance : DenselyOrdered BadFalse where dense := by intro a b h; exact ⟨a, trivial, trivial⟩

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target ← liftTermElabM <| elabType (← `(Nonempty BadFalse))
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

example : False := by
  -- try known interval theorem
  let a : BadFalse := Classical.choice (by infer_instance : Nonempty BadFalse)
  exact a.val
