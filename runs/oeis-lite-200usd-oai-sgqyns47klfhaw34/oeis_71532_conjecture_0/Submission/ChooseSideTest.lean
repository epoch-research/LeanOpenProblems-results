import FormalConjectures.Util.ProblemImports

noncomputable def side (P : Prop) : (P ∨ ¬ P) := Classical.em P

-- Can we project the true branch into an arbitrary fixed theorem? No, this should fail.
example (P : Prop) : P := by
  exact (Classical.em P).elim (fun hp => hp) (fun hnp => False.elim ?_)
