import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : NameSet := NameSet.empty.insert `propext |>.insert `Classical.choice |>.insert `Quot.sound
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    if shown > 200 then break
    let typeStr := toString ci.type
    if typeStr.contains "False" || typeStr.contains "∀ (P : Prop), P" || typeStr.contains "Inhabited" then
      let ax ← collectAxioms n
      let ok := ax.all (fun a => allowed.contains a)
      if ok then
        IO.println s!"{n} : {ci.type} axioms={ax.toList}"
        shown := shown + 1
