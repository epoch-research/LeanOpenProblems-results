import Submission.Spec

theorem disproof_test : ¬ (type_of% @oeis_a272979_conjecture_1) := by
  intro H
  have mem_magic_1211 : ((1, 2, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∈ a272979_magic_quadruples := by
    unfold a272979_magic_quadruples; simp
  have not_mem_magic_2111 : ((2, 1, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∉ a272979_magic_quadruples := by
    unfold a272979_magic_quadruples; simp
  have H1 := (H 1 2 1 1).mpr mem_magic_1211
  have H2 := (H 2 1 1 1).mp
  have H_repr_2111 : full_representability 2 1 1 1 := by
    unfold full_representability at H1 ⊢
    rcases H1 with ⟨_, _, _, _, h5⟩
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro n
    rcases h5 n with ⟨x, y, z, w, h_eq⟩
    use y, x, z, w
    linarith
  exact not_mem_magic_2111 (H2 H_repr_2111)
