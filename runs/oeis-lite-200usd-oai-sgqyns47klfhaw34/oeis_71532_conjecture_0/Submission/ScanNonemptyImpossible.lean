import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def isAllowedAx (n : Name) : Bool := n == `propext || n == `Classical.choice || n == `Quot.sound

#eval show CoreM Unit from do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    let axs ← Lean.collectAxioms n
    if !(axs.all isAllowedAx) then continue
    let ty := ci.type
    let s := toString ty
    if s.contains "Nonempty" && (s.contains "False" || s.contains "Empty" || s.contains "PUnit") then
      printed := printed + 1
      if printed < 200 then IO.println s!"{n} : {ty}"
  IO.println s!"printed {printed}"
