import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def conclusion (e : Expr) : Expr :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => conclusion b
  | Expr.letE _ _ v b _ => conclusion (b.instantiate1 v)
  | t => t.consumeMData

def hasName (nm : Name) (e : Expr) : Bool := e.getUsedConstants.contains nm

elab "#impossible_search" : command => do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 300 then break
    if n.isInternal then continue
    let c := conclusion ci.type
    let bad := hasName ``Nat.Prime c || hasName ``Subsingleton c || hasName ``Finite c || hasName ``Fintype c || hasName ``IsEmpty c || hasName ``Eq c
    if bad then
      let s := toString n
      if s.contains "false" || s.contains "False" || s.contains "one" || s.contains "zero" || s.contains "subsingleton" || s.contains "finite" || s.contains "Prime" || s.contains "Nat" then
        let pp ← liftTermElabM <| Meta.ppExpr ci.type
        logInfo m!"{n} : {pp}"
        printed := printed + 1
  logInfo m!"printed {printed}"

#impossible_search
