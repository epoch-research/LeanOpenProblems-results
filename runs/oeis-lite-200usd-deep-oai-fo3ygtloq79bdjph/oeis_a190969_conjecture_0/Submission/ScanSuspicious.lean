import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show CoreM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut cnt:=0
  for (n,ci) in (← getEnv).constants.toList do
    if n.isInternal then continue
    let ax ← collectAxioms n
    if !(ax.all fun a => allowed.contains a) then continue
    let t := ci.type
    let s := toString (← Meta.MetaM.run' <| ppExpr t)
    if (s.contains "∀ (P : Prop), P") || (s.contains "False") || (s.contains "0 = 1") || (s.contains "∀ (a b : ℕ), a = b") || (s.contains "Subsingleton Prop") then
      IO.println s!"{n} : {s} AX {ax}"
      cnt:=cnt+1
  IO.println s!"cnt={cnt}"
