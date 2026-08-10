import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command Term
open Lean.Elab

partial def stripForall (e : Expr) : Expr :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => stripForall b
  | Expr.letE _ _ v b _ => stripForall (b.instantiate1 v)
  | t => t.consumeMData

elab "#exact_danger_search" : command => do
  let dangersStx : Array (TSyntax `term) := #[
    ← `(Subsingleton ℕ), ← `(Subsingleton ℤ), ← `(Subsingleton ℚ), ← `(Subsingleton Prop),
    ← `(Finite ℕ), ← `(Fintype ℕ), ← `(IsEmpty True), ← `(IsEmpty ℕ),
    ← `(Nat.Prime 1), ← `(Nat.Prime 0), ← `((0 : ℕ) = 1), ← `((1 : ℕ) = 0),
    ← `((0 : ℤ) = 1), ← `((1 : ℤ) = 0), ← `((0 : ℚ) = 1), ← `((1 : ℚ) = 0),
    ← `((True : Prop) = False), ← `(¬ True), ← `(False)
  ]
  let mut dangers := #[]
  for stx in dangersStx do
    let e ← liftTermElabM <| Term.elabType stx
    dangers := dangers.push e
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let c := stripForall ci.type
    for d in dangers do
      if c == d then
        let pp ← liftTermElabM <| Meta.ppExpr ci.type
        logInfo m!"{n} : {pp}"
        printed := printed + 1
  logInfo m!"printed {printed}"

#exact_danger_search
