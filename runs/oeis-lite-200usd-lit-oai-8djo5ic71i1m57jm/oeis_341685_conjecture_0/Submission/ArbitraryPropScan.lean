import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
set_option maxHeartbeats 0

def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

partial def stripForalls : Expr → Array (Name × BinderInfo × Expr) → (Array (Name × BinderInfo × Expr) × Expr)
| .forallE n d b bi, acc => stripForalls b (acc.push (n,bi,d))
| .mdata _ e, acc => stripForalls e acc
| e, acc => (acc,e)

def isPropSort (e : Expr) : Bool :=
  match e.consumeMData with
  | .sort .zero => true
  | _ => false

def mentionsBVar0 (e : Expr) : Bool := e.hasLooseBVars

elab "#arbitrary_prop_scan" : command => do
  let env ← getEnv
  let mut printed : Nat := 0
  for (n, ci) in env.constants.toList do
    if printed >= 300 then break
    if n.isInternal then continue
    let ns := toString n
    if ns.contains "_proof" || ns.contains "match_" then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let (bs, concl) := stripForalls ci.type #[]
      -- Look for first binder p : Prop, and conclusion is just p (or Nonempty p/Inhabited p)
      let mut hasPropBinder := false
      for (_,_,d) in bs do
        if isPropSort d then hasPropBinder := true
      if hasPropBinder then
        let axs ← Lean.collectAxioms n
        if onlyAllowed axs then
          let pp ← liftTermElabM <| ppExpr ci.type
          let s := toString pp
          if s.contains "Prop" && (s.contains "Nonempty" || s.contains "Inhabited" || s.contains "False" || s.contains " → ") then
            logInfo m!"CAND {n} : {pp} | axioms {axs}"
            printed := printed + 1
    | _ => pure ()
  logInfo m!"printed {printed}"

#arbitrary_prop_scan
