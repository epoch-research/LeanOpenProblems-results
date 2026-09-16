import Submission.Spec

lemma mem_magic_1211 : ((1, 2, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∈ a272979_magic_quadruples := by
  unfold a272979_magic_quadruples
  simp

lemma not_mem_magic_2111 : ((2, 1, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∉ a272979_magic_quadruples := by
  unfold a272979_magic_quadruples
  simp

theorem disproof (H : ∀ a b c d : ℕ, full_representability a b c d ↔ (a, b, c, d) ∈ a272979_magic_quadruples) : False := by
  have H1 := (H 1 2 1 1).mpr mem_magic_1211
  have H2 := (H 2 1 1 1).mp
  have H_not_mem := not_mem_magic_2111
  have H_repr_2111 : full_representability 2 1 1 1 := by
    unfold full_representability at H1 ⊢
    rcases H1 with ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro n
    rcases h5 n with ⟨x, y, z, w, h_eq⟩
    use y, x, z, w
    linarith
  have contra := H2 H_repr_2111
  exact H_not_mem contra
