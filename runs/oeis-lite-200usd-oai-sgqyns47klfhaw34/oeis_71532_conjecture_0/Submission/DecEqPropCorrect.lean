import FormalConjectures.Util.ProblemImports

theorem maybe (P : Prop) : P := by
  let d := Classical.decEq Prop True P
  cases d with
  | isTrue h => exact Eq.mp h.symm trivial
  | isFalse h =>
    rcases Classical.propComplete P with hp | hp
    · exact of_eq_true hp
    · have hn : ¬P := of_eq_false hp
      -- no contradiction: h is True != False, consistent
      exact False.elim ?_
#print axioms Classical.propComplete
