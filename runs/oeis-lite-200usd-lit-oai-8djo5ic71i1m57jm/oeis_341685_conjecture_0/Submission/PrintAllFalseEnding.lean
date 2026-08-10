import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
set_option maxHeartbeats 0

def allowedAxioms : NameSet :=
  (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

partial def stripForallsSyntax : Expr → Expr
| .forallE _ _ b _ => stripForallsSyntax b
| .mdata _ e => stripForallsSyntax e
| e => e

def isFalseExpr (e : Expr) : Bool :=
  match e.consumeMData with | .const ``False _ => true | _ => false

elab "#print_all_false_ending" : command => do
  let env ← getEnv
  let mut printed : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      if isFalseExpr (stripForallsSyntax ci.type) then
        let axs ← Lean.collectAxioms n
        if onlyAllowed axs then
          let pp ← liftTermElabM <| ppExpr ci.type
          logInfo m!"idx {printed} name {n} : {pp} | axioms {axs}"
          printed := printed + 1
    | _ => pure ()
  logInfo m!"printed {printed}"

#print_all_false_ending
