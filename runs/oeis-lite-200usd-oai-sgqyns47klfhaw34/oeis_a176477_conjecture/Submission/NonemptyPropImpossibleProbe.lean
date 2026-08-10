import FormalConjectures.Util.ProblemImports
example (P : Prop) : Nonempty P := by
  classical
  rcases Classical.propComplete P with h | h
  · exact ⟨Eq.mp h.symm True.intro⟩
  · -- stuck: P = False
    subst P
    -- goal Nonempty False
    fail_if_success exact ⟨False.elim (by contradiction)⟩
    sorry
