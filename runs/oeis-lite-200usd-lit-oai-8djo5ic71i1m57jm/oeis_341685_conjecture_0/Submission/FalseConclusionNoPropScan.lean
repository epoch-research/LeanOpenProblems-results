import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

set_option maxHeartbeats 0

def allowedAxioms : NameSet :=
  (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

def isFalseExpr (e : Expr) : Bool :=
  match e.consumeMData with
  | .const ``False _ => true
  | _ => false

partial def collectBinders (type : Expr) (acc : Array (BinderInfo × Expr × Name)) : MetaM (Array (BinderInfo × Expr × Name) × Expr) := do
  let type ← whnf type
  match type with
  | .forallE n d b bi =>
      let x ← mkFreshExprMVar d .syntheticOpaque n
      collectBinders (b.instantiate1 x) (acc.push (bi,d,n))
  | _ => return (acc, type)

elab "#false_concl_scan" : command => do
  let env ← getEnv
  let mut printed := 0
  let mut total := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "FormalConjecturesForMathlib" || ns.startsWith "gold" || ns.startsWith "not_fermat" || ns.startsWith "Fermat" || ns.startsWith "CategoryTheory.zero_not_simple") then continue
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let axs ← Lean.collectAxioms n
      if onlyAllowed axs then
        try
          let (bs, concl) ← liftTermElabM <| collectBinders ci.type #[]
          if isFalseExpr concl then
            total := total + 1
            let mut hasOrdProp := false
            for (bi,d,_) in bs do
              if bi == BinderInfo.default then
                if ← liftTermElabM <| isProp d then
                  hasOrdProp := true
            if printed < 200 then
              let pp ← liftTermElabM <| ppExpr ci.type
              logInfo m!"CAND ordProp={hasOrdProp} {n} : {pp} | axioms {axs}"
              printed := printed + 1
        catch _ => pure ()
    | _ => pure ()
  logInfo m!"total false-concl {total}, printed {printed}"

#false_concl_scan
