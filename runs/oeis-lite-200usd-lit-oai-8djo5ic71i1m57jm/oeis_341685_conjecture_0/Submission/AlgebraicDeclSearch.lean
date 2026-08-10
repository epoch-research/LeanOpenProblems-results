import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def conclusion (e : Expr) : Expr :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => conclusion b
  | Expr.letE _ _ v b _ => conclusion (b.instantiate1 v)
  | t => t

def containsConst (nm : Name) (e : Expr) : Bool := (e.getUsedConstants).contains nm

elab "#alg_decl_search" : command => do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 300 then break
    if n.isInternal then continue
    let ty := ci.type
    if containsConst ``IsAlgebraic ty || containsConst ``Algebra.IsAlgebraic ty || containsConst ``Transcendental ty then
      let s := toString n
      if s.contains "Padic" || s.contains "padic" || s.contains "Algebraic" || s.contains "transcend" || s.contains "Transcend" || s.contains "IsIntegral" then
        let pp ← liftTermElabM <| Meta.ppExpr ty
        logInfo m!"{n} : {pp}"
        printed := printed + 1
  logInfo m!"printed {printed}"

#alg_decl_search
