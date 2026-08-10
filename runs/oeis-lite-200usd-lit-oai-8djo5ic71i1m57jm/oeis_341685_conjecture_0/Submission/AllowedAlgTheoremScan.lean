import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
set_option maxHeartbeats 0

def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)
partial def exprHasNamePart (parts : Array String) : Expr → Bool
| .const n _ => parts.any (fun p => n.toString.contains p)
| .app f a => exprHasNamePart parts f || exprHasNamePart parts a
| .lam _ t b _ => exprHasNamePart parts t || exprHasNamePart parts b
| .forallE _ t b _ => exprHasNamePart parts t || exprHasNamePart parts b
| .letE _ t v b _ => exprHasNamePart parts t || exprHasNamePart parts v || exprHasNamePart parts b
| .mdata _ e => exprHasNamePart parts e
| .proj _ _ e => exprHasNamePart parts e
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 500 then break
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      if exprHasNamePart #["IsAlgebraic", "Transcendental", "algebraicClosure", "aeval", "minpoly"] ci.type then
        let axs ← Lean.collectAxioms n
        if onlyAllowed axs then
          let pp ← liftTermElabM <| ppExpr ci.type
          logInfo m!"ALG {n} : {pp} | {axs}"
          printed := printed + 1
    | _ => pure ()
  logInfo m!"printed {printed}"
