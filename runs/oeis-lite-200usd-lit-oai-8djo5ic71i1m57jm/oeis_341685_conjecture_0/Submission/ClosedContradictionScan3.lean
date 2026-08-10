import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Term

set_option maxHeartbeats 0

unsafe def allowedArr (axs : Array Name) : Bool :=
  axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound

partial def exprSize : Expr → Nat
| .forallE _ d b _ => 1 + exprSize d + exprSize b
| .lam _ d b _ => 1 + exprSize d + exprSize b
| .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
| .app f a => 1 + exprSize f + exprSize a
| .mdata _ e => 1 + exprSize e
| .proj _ _ e => 1 + exprSize e
| _ => 1

unsafe def headName? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | .forallE .. => some `forall
  | _ => none

unsafe def scanClosedContradictions : TermElabM Unit := do
  let targetStx : List Syntax ← pure [
    (← `(False)),
    (← `((0 : ℕ) = 1)),
    (← `((1 : ℕ) = 0)),
    (← `((0 : ℤ) = 1)),
    (← `((0 : ℚ) = 1)),
    (← `((True : Prop) = False)),
    (← `((False : Prop) = True)),
    (← `(Subsingleton ℕ)),
    (← `(Subsingleton ℚ)),
    (← `(Finite ℕ)),
    (← `(Fintype ℕ)),
    (← `(IsEmpty ℕ)),
    (← `(Nonempty False)),
    (← `(Inhabited False)),
    (← `(Unique ℕ)),
    (← `(∀ n : ℕ, n = 0)),
    (← `(∀ q : ℚ, q = 0))
  ]
  let mut targets : Array (Expr × Option Name × Nat) := #[]
  for stx in targetStx do
    let e ← elabType stx
    targets := targets.push (e, headName? e, exprSize e)
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let axs ← Lean.collectAxioms n
      if allowedArr axs then
        let ty ← instantiateMVars ci.type
        let sz := exprSize ty
        if sz < 300 then
          let h := headName? ty
          for (t, ht, _) in targets do
            if h == ht then
              try
                let ok ← withReducible <| isDefEq ty t
                if ok then
                  logInfo m!"MATCH {n} : {← ppExpr ty} | axioms {axs}"
                  count := count + 1
              catch _ => pure ()
    | _ => pure ()
  logInfo m!"count {count}"

#eval! scanClosedContradictions
