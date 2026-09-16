import Submission.Spec

lemma P_symm (a b c d : ℕ) : represents_all_naturals a b c d → represents_all_naturals b a c d := by
  intro h n
  rcases h n with ⟨x, y, z, w, h_eq⟩
  use y, x, z, w
  dsimp [is_representable] at *
  linarith

theorem oeis_272979_conjecture_0_disproof : ¬ (∀ a b c d : ℕ, (a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) → (represents_all_naturals a b c d ↔ (a, b, c, d) ∈ sun_49_quadruples)) := by
  intro h
  have h1 := h 1 2 1 1 (by decide)
  have h2 := h 2 1 1 1 (by decide)
  have h1_in : (1, 2, 1, 1) ∈ sun_49_quadruples := by decide
  have h1_P : represents_all_naturals 1 2 1 1 := h1.mpr h1_in
  have h2_P : represents_all_naturals 2 1 1 1 := P_symm 1 2 1 1 h1_P
  have h2_in : (2, 1, 1, 1) ∈ sun_49_quadruples := h2.mp h2_P
  revert h2_in
  decide
