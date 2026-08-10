import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  let mut checked := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let s := toString ci.type
    let ns := toString name
    if !(s.contains "Nonempty" || s.contains "Inhabited" || s.contains "Decidable" || s.contains "∀ {α : Prop}" || s.contains "∀ (α : Prop)" || s.contains "∀ {P : Prop}" || s.contains "∀ (P : Prop)" || ns.contains "choice" || ns.contains "Complete" || ns.contains "indefinite") then
      continue
    checked := checked + 1
    let ax ← collectAxioms name
    if ax.all allowedAx then
      count := count + 1
      if shown < 500 then
        logInfo m!"{name} : {ci.type} AX {ax.toList}"
        shown := shown + 1
  logInfo m!"checked={checked}, count={count}, shown={shown}"
