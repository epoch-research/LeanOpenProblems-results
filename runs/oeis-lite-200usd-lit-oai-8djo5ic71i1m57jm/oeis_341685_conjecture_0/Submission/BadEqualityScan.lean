import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

set_option maxHeartbeats 0

def allowedAxioms : NameSet :=
  (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

partial def stripForallsSyntax : Expr → Array (BinderInfo × Expr × Name) → (Array (BinderInfo × Expr × Name) × Expr)
| .forallE n d b bi, acc => stripForallsSyntax b (acc.push (bi,d,n))
| .mdata _ e, acc => stripForallsSyntax e acc
| e, acc => (acc,e)

def isEqHead (e : Expr) : Bool :=
  match e.consumeMData.getAppFn with | .const ``Eq _ => true | _ => false

def exprHasConst (target : Name) (e : Expr) : Bool := e.getUsedConstants.contains target

elab "#bad_eq_scan" : command => do
  let env ← getEnv
  let mut total := 0
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let (bs, concl) := stripForallsSyntax ci.type #[]
      if isEqHead concl then
        let axs ← Lean.collectAxioms n
        if onlyAllowed axs then
          -- print small closed/non-prop-hyp equalities mentioning suspicious constants
          let mut hasDefaultProp := false
          for (bi,d,_) in bs do
            if bi == BinderInfo.default then
              try if ← liftTermElabM <| isProp d then hasDefaultProp := true catch _ => pure ()
          if !hasDefaultProp && (exprHasConst ``False concl || exprHasConst ``True concl || exprHasConst ``Nat concl || exprHasConst ``Bool concl || exprHasConst ``Subsingleton concl || exprHasConst ``Finite concl) then
            total := total + 1
            if printed < 500 then
              let pp ← liftTermElabM <| ppExpr ci.type
              logInfo m!"CAND {n} : {pp} | axioms {axs}"
              printed := printed + 1
    | _ => pure ()
  logInfo m!"total {total}, printed {printed}"

#bad_eq_scan
