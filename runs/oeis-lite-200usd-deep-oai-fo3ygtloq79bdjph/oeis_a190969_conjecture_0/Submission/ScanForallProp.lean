import FormalConjectures.Util.ProblemImports
open Lean Meta
partial def hasBadForall (e : Expr) : Bool :=
  match e with
  | .forallE _ dom body _ =>
      (dom == .sort .zero && body.hasLooseBVars) || hasBadForall body
  | _ => false
#eval show CoreM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut cnt:=0
  for (n,ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    if !hasBadForall ci.type then continue
    let ax ← collectAxioms n
    if ax.all (fun a => allowed.contains a) then
      IO.println s!"{n} : {← Meta.MetaM.run' <| ppExpr ci.type} AX {ax}"
      cnt:=cnt+1
      if cnt > 200 then break
  IO.println s!"cnt={cnt}"
