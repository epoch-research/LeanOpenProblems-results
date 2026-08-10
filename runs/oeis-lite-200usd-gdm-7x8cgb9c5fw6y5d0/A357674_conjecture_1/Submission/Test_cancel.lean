import FormalConjectures.Util.ProblemImports

lemma dvd_of_mul_dvd_mul_left {a b c : ℤ} (ha : a ≠ 0) (h : a * b ∣ a * c) : b ∣ c := by
  rcases h with ⟨k, hk⟩
  use k
  have h_eq : a * c = a * (b * k) := by
    calc a * c
      _ = a * b * k := hk
      _ = a * (b * k) := by ring
  exact mul_left_cancel₀ ha h_eq
