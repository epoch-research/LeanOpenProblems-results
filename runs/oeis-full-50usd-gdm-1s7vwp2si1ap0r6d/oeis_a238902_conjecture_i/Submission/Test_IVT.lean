import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

theorem discrete_ivt_interval (f : ℕ → ℕ) (n : ℕ) (h_step : ∀ x, f (x + 1) ≤ f x + n)
    (a : ℕ) (v : ℕ) : ∀ d, f a < v → v + n - 1 < f (a + d) →
    ∃ x ∈ Finset.Icc a (a + d), v ≤ f x ∧ f x ≤ v + n - 1 := by
  intro d
  induction d with
  | zero =>
    intro h1 h2
    simp only [add_zero] at h2
    omega
  | succ d ih =>
    intro h1 h2
    by_cases h_le : v + n - 1 < f (a + d)
    · have ih_res := ih h1 h_le
      rcases ih_res with ⟨x, hx, hx_range⟩
      use x
      simp only [Finset.mem_Icc] at hx ⊢
      refine ⟨⟨hx.1, hx.2.trans (Nat.le_succ _)⟩, hx_range⟩
    · push_neg at h_le
      have h_step_val := h_step (a + d)
      have h2_simped : v + n - 1 < f (a + d + 1) := by
        have h_eq_assoc : a + (d + 1) = a + d + 1 := by omega
        exact h_eq_assoc ▸ h2
      have h_eq : v ≤ f (a + d) ∧ f (a + d) ≤ v + n - 1 := by
        have h_step_val_rewrite : f (a + d + 1) ≤ f (a + d) + n := by
          have h_eq_assoc : a + d + 1 = (a + d) + 1 := by omega
          rw [h_eq_assoc] at h2_simped
          exact h_step (a + d)
        omega
      use a + d
      simp only [Finset.mem_Icc]
      refine ⟨by omega, h_eq⟩
