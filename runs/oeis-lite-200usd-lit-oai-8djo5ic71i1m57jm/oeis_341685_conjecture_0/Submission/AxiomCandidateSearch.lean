import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def hasConst (nm : Name) (e : Expr) : Bool := e.getUsedConstants.contains nm

partial def conclusion (e : Expr) : Expr :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => conclusion b
  | Expr.letE _ _ v b _ => conclusion (b.instantiate1 v)
  | t => t.consumeMData

elab "#candidate_search" : command => do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 500 then break
    if n.isInternal then continue
    let ty := ci.type
    let c := conclusion ty
    let nm := toString n
    let interesting :=
      hasConst ``Padic ty || hasConst ``IsAlgebraic ty || hasConst ``Algebra.IsAlgebraic ty ||
      hasConst ``Module.Finite ty || hasConst ``FiniteDimensional ty || hasConst ``Subsingleton ty ||
      hasConst ``Finite ty || hasConst ``Fintype ty || hasConst ``IsEmpty ty || hasConst ``False ty
    if interesting && (nm.contains "Padic" || nm.contains "padic" || nm.contains "Algebraic" || nm.contains "Finite" || nm.contains "Subsingleton" || nm.contains "false" || nm.contains "False") then
      let pp ← liftTermElabM <| Meta.ppExpr ty
      logInfo m!"{n} : {pp}"
      printed := printed + 1
  logInfo m!"printed {printed}"

#candidate_search
