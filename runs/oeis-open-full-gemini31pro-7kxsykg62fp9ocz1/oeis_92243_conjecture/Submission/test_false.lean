import Submission.Spec

theorem disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  rcases h with ⟨h1, ⟨B_low, h2⟩, ⟨B_high, h3⟩, h4, h5⟩
  sorry
