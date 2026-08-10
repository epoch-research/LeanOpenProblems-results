import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

set_option maxHeartbeats 0

def allowedAxioms : NameSet :=
  (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

def isConstName (e : Expr) (n : Name) : Bool :=
  match e.consumeMData with | .const m _ => m == n | _ => false

partial def stripForallsSyntax : Expr → Array (BinderInfo × Expr × Name) → (Array (BinderInfo × Expr × Name) × Expr)
| .forallE n d b bi, acc => stripForallsSyntax b (acc.push (bi,d,n))
| .mdata _ e, acc => stripForallsSyntax e acc
| e, acc => (acc,e)

elab "#fast_false_end_scan" : command => do
  let env ← getEnv
  let mut raw : Array (Name × Expr × Array (BinderInfo × Expr × Name)) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let (bs, concl) := stripForallsSyntax ci.type #[]
      if isConstName concl ``False then
        raw := raw.push (n, ci.type, bs)
    | _ => pure ()
  logInfo m!"raw false-ending {raw.size}"
  let mut printed := 0
  let mut allowed := 0
  for (n, ty, bs) in raw do
    let axs ← Lean.collectAxioms n
    if onlyAllowed axs then
      allowed := allowed + 1
      let mut hasDefaultProp := false
      for (bi,d,_) in bs do
        if bi == BinderInfo.default then
          try
            if ← liftTermElabM <| isProp d then hasDefaultProp := true
          catch _ => pure ()
      if !hasDefaultProp && printed < 500 then
        let pp ← liftTermElabM <| ppExpr ty
        logInfo m!"CAND {n} : {pp} | axioms {axs}"
        printed := printed + 1
  logInfo m!"allowed {allowed}, printed {printed}"

#fast_false_end_scan
