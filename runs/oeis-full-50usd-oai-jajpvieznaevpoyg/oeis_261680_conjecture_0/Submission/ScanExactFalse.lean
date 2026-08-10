import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : NameSet := NameSet.empty.insert `propext |>.insert `Classical.choice |>.insert `Quot.sound
  let nonemptyFalse := mkApp (mkConst ``Nonempty [levelZero]) (mkConst ``False)
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t == mkConst ``False || t == nonemptyFalse then
      let ax ← collectAxioms n
      if ax.all (fun a => allowed.contains a) then
        IO.println s!"{n} : {ci.type} axioms={ax.toList}"
        shown := shown + 1
  IO.println s!"shown {shown}"
