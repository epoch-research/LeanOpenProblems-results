import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

elab "#allowed_prop_eq_search_fast" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    let mut checked := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let s := toString ci.type
      let ns := toString name
      if !((s.contains "∀ {P : Prop}" || s.contains "∀ (P : Prop)" ||
            s.contains "∀ {p : Prop}" || s.contains "∀ (p : Prop)" ||
            s.contains "Prop →" || s.contains "P = True" || s.contains "P = False" ||
            s.contains "= True" || s.contains "= False" || s.contains "True =" || s.contains "False =" ||
            s.contains "Nonempty" || s.contains "Inhabited" || ns.contains "prop" || ns.contains "Prop" ||
            ns.contains "complete" || ns.contains "choice" || ns.contains "em")) then continue
      checked := checked + 1
      let ax ← collectAxioms name
      if ax.all allowedAx then
        if shown < 1000 then
          logInfo m!"{name} : {ci.type} AX {ax.toList}"
          shown := shown + 1
    logInfo m!"checked={checked} shown={shown}"

#allowed_prop_eq_search_fast
