import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

open Lean Meta Elab Command Term

partial def forallTelescopeReducingAux (type : Expr) (k : Nat) (xs : Array Expr) : MetaM (Array Expr × Expr) := do
  if k == 0 then return (xs, type)
  let type ← whnf type
  match type with
  | Expr.forallE n d b _ =>
    let x ← mkFreshExprMVar d MetavarKind.syntheticOpaque n
    forallTelescopeReducingAux (b.instantiate1 x) (k-1) (xs.push x)
  | _ => return (xs,type)

elab "#unify_apply_search" : command => do
  let targetsStx : Array (TSyntax `term) := #[← `(IsAlgebraic ℚ xi_3), ← `(¬ IsAlgebraic ℚ xi_3), ← `(False)]
  let mut targets := #[]
  for stx in targetsStx do
    targets := targets.push (← liftTermElabM <| Term.elabType stx)
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 100 then break
    if n.isInternal then continue
    let ns := toString n
    if ns.contains "match_" || ns.contains "noConfusion" || ns.contains ".rec" then continue
    let mut found := false
    for maxArgs in [0:8] do
      if found then continue
      try
        let (_, concl) ← liftTermElabM <| forallTelescopeReducingAux ci.type maxArgs #[]
        for tgt in targets do
          if !found && (← liftTermElabM <| isDefEq concl tgt) then
            let pp ← liftTermElabM <| Meta.ppExpr ci.type
            logInfo m!"CAND args≤{maxArgs}: {n} : {pp}"
            printed := printed + 1
            found := true
      catch _ => pure ()
  logInfo m!"printed {printed}"

#unify_apply_search
