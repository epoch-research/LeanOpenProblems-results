import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
partial def hasConst (nm : Name) (e : Expr) : Bool := e.getUsedConstants.contains nm
partial def conclusion (e : Expr) : Expr :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => conclusion b
  | Expr.letE _ _ v b _ => conclusion (b.instantiate1 v)
  | t => t.consumeMData

elab "#trans_decl_search" : command => do
  let env ← getEnv
  let mut arr : Array (Name × Expr) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let ty := ci.type
    if hasConst ``Transcendental ty || (hasConst ``IsAlgebraic ty && hasConst ``Not ty) then
      arr := arr.push (n,ty)
  let mut printed := 0
  for (n, ty) in arr do
    if printed >= 500 then break
    let nm := toString n
    if nm.contains "transcend" || nm.contains "Transcend" || nm.contains "Algebraic" || nm.contains "isAlgebraic" || nm.contains "not" then
      let pp ← liftTermElabM <| Meta.ppExpr ty
      logInfo m!"{n} : {pp}"
      printed := printed + 1
  logInfo m!"total {arr.size}, printed {printed}"
#trans_decl_search
