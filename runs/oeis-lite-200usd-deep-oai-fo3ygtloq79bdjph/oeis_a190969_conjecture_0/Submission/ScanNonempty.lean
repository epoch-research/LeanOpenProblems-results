import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show CoreM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut cnt := 0
  for (n,ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    let st := toString (← Meta.MetaM.run' <| ppExpr ci.type)
    if st.contains "Nonempty" && st.contains "Prop" then
      let ax ← collectAxioms n
      if ax.all (fun a => allowed.contains a) then
        IO.println s!"{n} : {st} AX {ax}"
        cnt := cnt+1
        if cnt > 200 then break
  IO.println s!"cnt={cnt}"
