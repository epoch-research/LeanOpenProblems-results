import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  liftTermElabM <| do
    let n := ``top_nonempty
    let ci ← getConstInfo n
    let us := ci.levelParams.map (fun _ => levelZero)
    let c := mkConst n us
    let ty ← inferType c
    logInfo m!"ty {← ppExpr ty}"
    let (xs, bis, body) ← forallMetaTelescopeReducing ty
    logInfo m!"xs {xs.size}, body {← ppExpr body}"
    let target := mkApp (mkConst ``Nonempty [levelOne]) (mkConst ``Empty)
    let ok ← isDefEq body target
    logInfo m!"ok {ok}, body2 {← ppExpr (← instantiateMVars body)} target {← ppExpr target}"
