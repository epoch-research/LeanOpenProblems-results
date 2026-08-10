import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show CoreM Unit from do
  let allowedList := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    let s := toString ci.type
    if s.contains "False" then
      let ax ← collectAxioms n
      if ax.all (fun a => allowedList.contains a) then
        IO.println s!"{n} : {ci.type} AX {ax}"
        count := count+1
  IO.println s!"false count {count}"
