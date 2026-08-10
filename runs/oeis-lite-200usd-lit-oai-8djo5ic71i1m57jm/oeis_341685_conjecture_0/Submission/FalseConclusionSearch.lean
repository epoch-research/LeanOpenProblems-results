import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def conclusion (e : Expr) : Expr :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => conclusion b
  | Expr.letE _ _ v b _ => conclusion (b.instantiate1 v)
  | t => t

partial def countForalls (e : Expr) : Nat :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => countForalls b + 1
  | _ => 0

elab "#false_conclusion_search" : command => do
  let env ← getEnv
  let mut arr : Array (Nat × Name × Expr) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if (conclusion ci.type).consumeMData.isConstOf ``False then
      arr := arr.push (countForalls ci.type, n, ci.type)
  let sorted := arr.qsort (fun a b => a.1 < b.1)
  let mut printed := 0
  for (_, n, ty) in sorted do
    if printed >= 300 then break
    let pp ← liftTermElabM <| Meta.ppExpr ty
    logInfo m!"{n} : {pp}"
    printed := printed + 1
  logInfo m!"total false-conclusion {arr.size}, printed {printed}"

#false_conclusion_search
