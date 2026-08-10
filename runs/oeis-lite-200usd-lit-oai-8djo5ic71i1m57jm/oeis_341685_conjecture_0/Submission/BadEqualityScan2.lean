import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

set_option maxHeartbeats 0

def allowedAxioms : NameSet :=
  (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

partial def exprSize : Expr → Nat
| .forallE _ d b _ => 1 + exprSize d + exprSize b
| .lam _ d b _ => 1 + exprSize d + exprSize b
| .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
| .app f a => 1 + exprSize f + exprSize a
| .mdata _ e => 1 + exprSize e
| .proj _ _ e => 1 + exprSize e
| _ => 1

partial def stripForallsSyntax : Expr → Array (BinderInfo × Expr × Name) → (Array (BinderInfo × Expr × Name) × Expr)
| .forallE n d b bi, acc => stripForallsSyntax b (acc.push (bi,d,n))
| .mdata _ e, acc => stripForallsSyntax e acc
| e, acc => (acc,e)

def isEqHead (e : Expr) : Bool :=
  match e.consumeMData.getAppFn with | .const ``Eq _ => true | _ => false

def hasSuspiciousConst (e : Expr) : Bool :=
  let cs := e.getUsedConstants
  cs.contains ``False || cs.contains ``True || cs.contains ``Nat || cs.contains ``Bool || cs.contains ``Int || cs.contains ``Rat

elab "#bad_eq_scan2" : command => do
  let env ← getEnv
  let mut pre := 0
  let mut total := 0
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let (bs, concl) := stripForallsSyntax ci.type #[]
      if isEqHead concl && exprSize ci.type < 250 && hasSuspiciousConst concl then
        pre := pre + 1
        let axs ← Lean.collectAxioms n
        if onlyAllowed axs then
          let mut hasDefaultProp := false
          for (bi,d,_) in bs do
            if bi == BinderInfo.default then
              try if ← liftTermElabM <| isProp d then hasDefaultProp := true catch _ => pure ()
          if !hasDefaultProp then
            total := total + 1
            if printed < 500 then
              let pp ← liftTermElabM <| ppExpr ci.type
              logInfo m!"CAND {n} : {pp} | axioms {axs}"
              printed := printed + 1
    | _ => pure ()
  logInfo m!"pre {pre}, total {total}, printed {printed}"

#bad_eq_scan2
