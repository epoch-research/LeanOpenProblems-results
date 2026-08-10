import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAxiomName (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    if shown < 120 then
      let s := toString ci.type
      if !(s.contains "∀") && !(s.contains "→") && s.contains "ℕ" &&
          (s.contains "= 0" || s.contains "= 1" || s.contains "<" || s.contains "≤") then
        let axs ← liftCoreM <| collectAxioms n
        if axs.all allowedAxiomName then
          shown := shown + 1
          logInfo m!"{n} axs={axs} : {ci.type}"
  logInfo m!"shown {shown}"
