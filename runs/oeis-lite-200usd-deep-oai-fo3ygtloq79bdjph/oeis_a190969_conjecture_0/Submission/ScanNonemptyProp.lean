import FormalConjectures.Util.ProblemImports
open Lean Meta
partial def isNonemptyApp : Expr → Bool
| .app (.const ``Nonempty _) (.sort .zero) => true
| _ => false
partial def hasNonemptyProp : Expr → Bool
| .forallE _ d b _ => isNonemptyApp d || hasNonemptyProp b
| e => isNonemptyApp e
#eval show CoreM Unit from do
  let allowedList := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    if hasNonemptyProp ci.type then
      let ax ← collectAxioms n
      if ax.all (fun a => allowedList.contains a) then
        IO.println s!"{n} : {ci.type} AX {ax}"
        count := count + 1
        if count > 200 then return
  IO.println s!"count {count}"
