import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show CoreM Unit from do
  let allowedList := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    let ax ← collectAxioms n
    if ax.all (fun a => allowedList.contains a) then
      let t := ci.type
      let s := toString t
      if s.contains "∀" && s.contains "Prop" && (s.endsWith "P" || s.contains "→ P" || s.contains "False") then
        IO.println s!"{n} : {t} AX {ax}"
        count := count+1
        if count > 500 then return
  IO.println s!"count {count}"
