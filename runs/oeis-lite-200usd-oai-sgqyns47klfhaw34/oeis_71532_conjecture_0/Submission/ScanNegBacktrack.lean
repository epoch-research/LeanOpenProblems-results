import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 12000000
open Lean Meta Elab Command

partial def typeCandidates (ty : Expr) : MetaM (Array Expr) := do
  let tyw ← whnf ty
  let mut arr : Array Expr := #[]
  if (← isDefEq tyw (mkSort levelZero)) then
    arr := arr.push (mkConst ``True)
    arr := arr.push (mkConst ``False)
  match tyw with
  | Expr.sort u =>
      if !u.isZero then
        arr := arr.push (mkConst ``PUnit [levelZero])
        arr := arr.push (mkConst ``Unit)
        arr := arr.push (mkConst ``Empty)
        arr := arr.push (mkConst ``Bool)
        arr := arr.push (mkConst ``Nat)
        arr := arr.push (mkConst ``Int)
        arr := arr.push (mkSort levelZero)
        arr := arr.push (mkApp (mkConst ``ZMod) (mkNatLit 1))
        arr := arr.push (mkApp (mkConst ``ZMod) (mkNatLit 8))
  | _ => pure ()
  return arr

partial def termCandidates (ty : Expr) : MetaM (Array Expr) := do
  let ty ← whnf ty
  let mut arr : Array Expr := #[]
  try arr := arr.push (← synthInstance ty) catch _ => pure ()
  try arr := arr.push (← mkAppM ``default #[ty]) catch _ => pure ()
  if (← isDefEq ty (mkConst ``Nat)) then arr := arr.push (mkNatLit 0); arr := arr.push (mkNatLit 1); arr := arr.push (mkNatLit 2)
  if (← isDefEq ty (mkConst ``Bool)) then arr := arr.push (mkConst ``Bool.false); arr := arr.push (mkConst ``Bool.true)
  if (← isDefEq ty (mkConst ``Int)) then arr := arr.push (toExpr (0 : Int)); arr := arr.push (toExpr (1 : Int)); arr := arr.push (toExpr (-1 : Int))
  arr := arr ++ (← typeCandidates ty)
  return arr

partial def searchArgs (xs : Array Expr) (i : Nat) (prev : Array Expr) (args : Array Expr) (body : Expr)
    (k : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  if h : i < xs.size then
    let x := xs[i]
    let d ← x.fvarId!.getDecl
    if d.binderInfo == BinderInfo.default then return ()
    let ty := d.type.replaceFVars prev args
    let cands ← termCandidates ty
    for e in cands do
      searchArgs xs (i+1) (prev.push x) (args.push e) body k
  else
    k args (body.replaceFVars prev args)

elab "#scan_neg_backtrack" : command => do
  liftTermElabM do
    let env ← getEnv
    let printedRef ← IO.mkRef (0 : Nat)
    for (n, ci) in env.constants.toList do
      if (← printedRef.get) > 200 then return ()
      forallTelescope ci.type fun xs body => do
        if xs.size == 0 || xs.size > 6 then return ()
        unless body.isAppOfArity ``Not 1 do return ()
        searchArgs xs 0 #[] #[] body fun args b => do
          unless b.isAppOfArity ``Not 1 do return ()
          let p := b.appArg!
          try
            let _ ← synthInstance (← mkAppM ``Decidable #[p])
            let d ← mkAppM ``decide #[p]
            let dv ← whnf d
            if dv.isConstOf ``true then
              let app := mkAppN (mkConst n (ci.levelParams.map Level.param)) args
              printedRef.modify (· + 1)
              logInfo m!"NEG_BACKTRACK {n}\n  app={app}\n  P={p}"
          catch _ => pure ()

#scan_neg_backtrack
