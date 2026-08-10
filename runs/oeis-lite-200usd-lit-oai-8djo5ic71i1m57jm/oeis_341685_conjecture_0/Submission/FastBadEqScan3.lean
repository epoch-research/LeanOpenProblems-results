import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
set_option maxHeartbeats 0

def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

partial def exprSize : Expr → Nat
| .forallE _ d b _ => 1 + exprSize d + exprSize b
| .lam _ d b _ => 1 + exprSize d + exprSize b
| .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
| .app f a => 1 + exprSize f + exprSize a
| .mdata _ e => 1 + exprSize e
| .proj _ _ e => 1 + exprSize e
| _ => 1

partial def stripForalls : Expr → Array (BinderInfo × Expr) → (Array (BinderInfo × Expr) × Expr)
| .forallE _ d b bi, acc => stripForalls b (acc.push (bi,d))
| .mdata _ e, acc => stripForalls e acc
| e, acc => (acc,e)

def eqArgs? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.consumeMData with
  | .app (.app (.app (.const ``Eq _) ty) lhs) rhs => some (ty,lhs,rhs)
  | _ => none

def constHeadName? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn with | .const n _ => some n | _ => none

def suspiciousEq (ty lhs rhs : Expr) : Bool :=
  let cty := constHeadName? ty
  (cty == some ``Nat || cty == some ``Int || cty == some ``Rat || cty == some ``Bool) ||
  lhs.getUsedConstants.contains ``False || rhs.getUsedConstants.contains ``False ||
  lhs.getUsedConstants.contains ``True || rhs.getUsedConstants.contains ``True

elab "#fast_bad_eq_scan3" : command => do
  let env ← getEnv
  let mut pre : Nat := 0
  let mut total : Nat := 0
  let mut printed : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let ns := toString n
    if !(ns.startsWith "FormalConjecturesForMathlib" || ns.startsWith "gold" || ns.startsWith "Fermat" || ns.startsWith "not_fermat" || ns.startsWith "Lean.Grind" || ns.startsWith "Mathlib.Tactic" || ns.startsWith "Int.Linear" || ns.startsWith "Nat.prime") then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      if exprSize ci.type > 220 then continue
      let (bs, concl) := stripForalls ci.type #[]
      match eqArgs? concl with
      | some (ty,lhs,rhs) =>
        if suspiciousEq ty lhs rhs then
          pre := pre + 1
          let axs ← Lean.collectAxioms n
          if onlyAllowed axs then
            let mut hasDefaultProp := false
            for (bi,d) in bs do
              if bi == BinderInfo.default then
                try if ← liftTermElabM <| isProp d then hasDefaultProp := true catch _ => pure ()
            if !hasDefaultProp then
              total := total + 1
              if printed < 300 then
                let pp ← liftTermElabM <| ppExpr ci.type
                logInfo m!"CAND {n} : {pp} | axioms {axs}"
                printed := printed + 1
      | none => pure ()
    | _ => pure ()
  logInfo m!"pre {pre}, total {total}, printed {printed}"

#fast_bad_eq_scan3
