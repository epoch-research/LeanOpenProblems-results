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

elab "#fast_target_scan" : command => do
  let targetsStx : Array (TSyntax `term) := #[
    ← `(IsAlgebraic ℚ xi_3), ← `(¬ IsAlgebraic ℚ xi_3), ← `(¬ (¬ IsAlgebraic ℚ xi_3)),
    ← `(Algebra.IsAlgebraic ℚ (Padic 3)), ← `(Module.Finite ℚ (Padic 3)), ← `(False)]
  let mut targets := #[]
  for stx in targetsStx do targets := targets.push (← liftTermElabM <| Term.elabType stx)
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 200 then break
    if n.isInternal then continue
    let ns := toString n
    if ns.contains "rec" || ns.contains "match" || ns.contains "noConfusion" then continue
    let cs := ci.type.getUsedConstants
    if !(cs.contains ``IsAlgebraic || cs.contains ``Transcendental || cs.contains ``Algebra.IsAlgebraic || cs.contains ``Module.Finite || cs.contains ``False) then continue
    let mut found := false
    for maxArgs in [0:10] do
      if found then continue
      try
        let (_, concl) ← liftTermElabM <| forallTelescopeReducingAux ci.type maxArgs #[]
        for tgt in targets do
          if !found && (← liftTermElabM <| isDefEq concl tgt) then
            let pp ← liftTermElabM <| Meta.ppExpr ci.type
            logWarning m!"UNIFY args≤{maxArgs}: {n} : {pp}"
            printed := printed + 1
            found := true
      catch _ => pure ()
  logWarning m!"printed {printed}"
#fast_target_scan
