import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := [`false_of_nontrivial_of_subsingleton, `not_finite, `Finite.false, `Infinite.false, `CharP.false_of_nontrivial_of_char_one]
  for n in names do
    try
      let ci ← getConstInfo n
      let ax ← collectAxioms n
      logInfo m!"{n}: {ci.type} AX {ax.toList} allowed={ax.all allowedAx}"
    catch e => logInfo m!"missing {n}: {e.toMessageData}"
