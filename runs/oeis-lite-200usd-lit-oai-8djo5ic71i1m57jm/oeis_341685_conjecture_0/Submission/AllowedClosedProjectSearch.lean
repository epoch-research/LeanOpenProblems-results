import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAxioms : NameSet :=
  (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

def hasForallHead (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.forallE .. => true
  | _ => false

elab "#allowed_closed_project_search" : command => do
  let env ← getEnv
  let mut arr : Array (Name × Expr × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if !(ns.startsWith "FormalConjectures" || ns.startsWith "Nat." || ns.startsWith "Real." || ns.startsWith "gold" || ns.startsWith "Fermat") then continue
    if n.isInternal then continue
    if hasForallHead ci.type then continue
    if (← liftTermElabM <| isProp ci.type) then
      let axs ← Lean.collectAxioms n
      if onlyAllowed axs then
        arr := arr.push (n, ci.type, axs)
  let mut printed := 0
  for (n, ty, axs) in arr do
    if printed >= 500 then break
    let pp ← liftTermElabM <| Meta.ppExpr ty
    logInfo m!"{n} : {pp} | axioms {axs.toList}"
    printed := printed + 1
  logInfo m!"total {arr.size}, printed {printed}"

#allowed_closed_project_search
