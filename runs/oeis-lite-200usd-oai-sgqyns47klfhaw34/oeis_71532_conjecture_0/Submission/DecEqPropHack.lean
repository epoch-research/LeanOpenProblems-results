import FormalConjectures.Util.ProblemImports
axiom P : Prop
example : P := by
  have d := Classical.decEq True P
  cases d with
  | isTrue h => exact Eq.mp h.symm trivial
  | isFalse h =>
      -- h : True ≠ P, but propComplete says P=True or False
      rcases Classical.propComplete P with hp | hp
      · exact Eq.mp hp.symm trivial
      · have hn : ¬ P := of_eq_false hp
        -- no contradiction
        exact False.elim ?_
