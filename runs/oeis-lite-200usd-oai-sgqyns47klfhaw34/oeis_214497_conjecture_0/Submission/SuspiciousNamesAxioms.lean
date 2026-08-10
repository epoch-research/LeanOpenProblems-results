import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let candidates := [`false_of_nontrivial_of_subsingleton, `not_finite, `Finite.false, `Infinite.false,
    `CharP.false_of_nontrivial_of_char_one, `not_preirreducible_nontrivial_t2,
    `Classical.byContradiction, `Classical.byContradiction', `Classical.propComplete,
    `false_of_true_eq_false, `false_of_true_iff_false, `true_iff_false, `false_iff_true,
    `neZero_zero_iff_false, `CategoryTheory.zero_not_simple]
  for n in candidates do
    try
      let ci ← getConstInfo n
      let ax ← collectAxioms n
      logInfo m!"{n}: {ci.type} AX={ax.toList} allowed={ax.all allowedAx}"
    catch e => logInfo m!"missing {n}: {e.toMessageData}"
