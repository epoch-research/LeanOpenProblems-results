import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
set_option maxHeartbeats 0

def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

partial def strip : Expr → Array Expr → (Array Expr × Expr)
| .forallE _ d b _, acc => strip b (acc.push d)
| .mdata _ e, acc => strip e acc
| e, acc => (acc,e)

def isPropSort : Expr → Bool
| .sort .zero => true
| .mdata _ e => isPropSort e
| _ => false

def isBVarConclusion : Expr → Bool
| .bvar _ => true
| .mdata _ e => isBVarConclusion e
| _ => false

elab "#prop_concl_scan" : command => do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 500 then break
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let (bs, concl) := strip ci.type #[]
      if isBVarConclusion concl then
        -- at least one prop binder
        if bs.any isPropSort then
          let axs ← Lean.collectAxioms n
          if onlyAllowed axs then
            let pp ← liftTermElabM <| ppExpr ci.type
            logInfo m!"CAND {n} : {pp} | {axs}"
            printed := printed + 1
    | _ => pure ()
  logInfo m!"printed {printed}"

#prop_concl_scan
