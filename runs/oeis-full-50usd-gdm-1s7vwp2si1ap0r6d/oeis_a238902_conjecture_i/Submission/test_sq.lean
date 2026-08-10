import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

theorem square_exists_of_step_le (f : ℕ → ℕ) (n : ℕ)
    (h_mono : ∀ i, f i ≤ f (i + 1))
    (h_step : ∀ i, f (i + 1) ≤ ((f i).sqrt + 1) ^ 2)
    (h_range : (f 0).sqrt < (f n).sqrt) :
    ∃ i ≤ n, (f i).sqrt ^ 2 = f i := by
  by_contra h_all
  push_neg at h_all
  have h_not_sq : ∀ i ≤ n, (f i).sqrt ^ 2 < f i := by
    intro i hi
    have h1 := h_all i hi
    have h2 := Nat.sqrt_le' (f i)
    omega
  have h_sqrt_eq : ∀ i ≤ n, (f i).sqrt = (f 0).sqrt := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro h_le
      have h_le_prev : i ≤ n := by omega
      have ih_val := ih h_le_prev
      have h_mono_step := h_mono i
      have h_sqrt_mono : (f i).sqrt ≤ (f (i + 1)).sqrt := Nat.sqrt_le_sqrt h_mono_step
      have h_step_val := h_step i
      have h_sqrt_succ : (f (i + 1)).sqrt ≤ (f i).sqrt + 1 := by
        have h1 : (f (i + 1)).sqrt ≤ (((f i).sqrt + 1) ^ 2).sqrt := Nat.sqrt_le_sqrt h_step_val
        rw [Nat.sqrt_eq'] at h1
        exact h1
      by_cases h_eq_succ : (f (i + 1)).sqrt = (f i).sqrt + 1
      · have h_sq_eq : (f (i + 1)).sqrt ^ 2 = f (i + 1) := by
          have h1 : (f (i + 1)).sqrt ^ 2 = ((f i).sqrt + 1) ^ 2 := by rw [h_eq_succ]
          have h2 : (f (i + 1)).sqrt ^ 2 ≤ f (i + 1) := Nat.sqrt_le' (f (i + 1))
          have h3 : f (i + 1) ≤ (f (i + 1)).sqrt ^ 2 := by
            rw [h1]
            exact h_step_val
          omega
        have h_not_sq_val := h_not_sq (i + 1) h_le
        omega
      · omega
  have h_fn_eq := h_sqrt_eq n (le_refl n)
  omega
