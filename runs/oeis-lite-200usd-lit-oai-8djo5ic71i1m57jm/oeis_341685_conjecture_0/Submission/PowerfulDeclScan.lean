import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
open Lean Meta Elab Command Term

unsafe def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
unsafe def onlyAllowedDecl (n : Name) : CoreM Bool := do
  let axs ← collectAxioms n
  return axs.all (allowedAxioms.contains ·)

partial def stripForalls (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE _ _ b _ => stripForalls b
  | .letE _ _ _ b _ => stripForalls b
  | x => x

elab "#powerful_decl_scan" : command => unsafe do
  let targetsStx : Array (TSyntax `term) := #[
    ← `(Module.Finite ℚ (Padic 3)),
    ← `(FiniteDimensional ℚ (Padic 3)),
    ← `(Algebra.IsAlgebraic ℚ (Padic 3)),
    ← `(IsAlgebraic ℚ xi_3),
    ← `(¬ IsAlgebraic ℚ xi_3),
    ← `(Subsingleton (Padic 3)),
    ← `(Finite (Padic 3)),
    ← `(Fintype (Padic 3)),
    ← `(Countable (Padic 3)),
    ← `((0 : Padic 3) = 1),
    ← `((0 : ℚ) = 1),
    ← `(False)
  ]
  let mut targets := #[]
  for stx in targetsStx do targets := targets.push (← liftTermElabM <| Term.elabType stx)
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count >= 300 then break
    if n.isInternal then continue
    if !(← liftCoreM <| onlyAllowedDecl n) then continue
    let concl := stripForalls ci.type
    let mut found := false
    for tgt in targets do
      if !found then
        try
          if ← liftTermElabM <| isDefEq concl tgt then
            logWarning m!"POWER {n} : {ci.type} | concl {concl}"
            count := count + 1
            found := true
        catch _ => pure ()
  logWarning m!"printed {count}"
#powerful_decl_scan
