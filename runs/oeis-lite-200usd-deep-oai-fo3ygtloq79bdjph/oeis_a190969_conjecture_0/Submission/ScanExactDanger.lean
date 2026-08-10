import FormalConjectures.Util.ProblemImports
open Lean Meta
partial def targetLike : Expr → Bool
| .forallE _ d b _ =>
    (d.isSort && b.hasLooseBVar 0) || targetLike b
| .sort .zero => true
| _ => false
#eval show CoreM Unit from do
  let allowedList := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    let t := ci.type
    -- print theorem with False anywhere and allowed
    if Lean.Expr.hasConst t ``False || toString t |>.contains "False" then
      let ax ← collectAxioms n
      if ax.all (fun a => allowedList.contains a) then
        IO.println s!"{n} : {t} AX {ax}"
        count := count+1
  IO.println s!"false count {count}"
