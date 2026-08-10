import FormalConjectures.Util.ProblemImports

lemma test_algebra_even (m : ℕ) (T : ℤ) (hm_ge : 12 ≤ m) (h_rel1 : 2 * T ≥ (m : ℤ) + 2) (h_rel2 : 2 * T ≤ (m : ℤ) + 3) :
  4 * (m : ℤ)^3 - 6 * (m : ℤ)^2 + 8 * (m : ℤ) - 12 * (m : ℤ) * ((m : ℤ) - 1 - T) * ((m : ℤ) - T) ≤ 12 * (m : ℤ)^2 - 6 := by
  have h_cases : 2 * T = (m : ℤ) + 2 ∨ 2 * T = (m : ℤ) + 3 := by omega
  rcases h_cases with h1 | h2
  · have h_eq : 12 * (m : ℤ) * ((m : ℤ) - 1 - T) * ((m : ℤ) - T) = 3 * (m : ℤ) * ((m : ℤ) - 4) * ((m : ℤ) - 2) := by
      calc 12 * (m : ℤ) * ((m : ℤ) - 1 - T) * ((m : ℤ) - T)
        _ = 3 * (m : ℤ) * (2 * (m : ℤ) - 2 - 2 * T) * (2 * (m : ℤ) - 2 * T) := by ring
        _ = 3 * (m : ℤ) * (2 * (m : ℤ) - 2 - ((m : ℤ) + 2)) * (2 * (m : ℤ) - ((m : ℤ) + 2)) := by rw [h1]
        _ = 3 * (m : ℤ) * ((m : ℤ) - 4) * ((m : ℤ) - 2) := by ring
    rw [h_eq]
    nlinarith
  · have h_eq : 12 * (m : ℤ) * ((m : ℤ) - 1 - T) * ((m : ℤ) - T) = 3 * (m : ℤ) * ((m : ℤ) - 5) * ((m : ℤ) - 3) := by
      calc 12 * (m : ℤ) * ((m : ℤ) - 1 - T) * ((m : ℤ) - T)
        _ = 3 * (m : ℤ) * (2 * (m : ℤ) - 2 - 2 * T) * (2 * (m : ℤ) - 2 * T) := by ring
        _ = 3 * (m : ℤ) * (2 * (m : ℤ) - 2 - ((m : ℤ) + 3)) * (2 * (m : ℤ) - ((m : ℤ) + 3)) := by rw [h2]
        _ = 3 * (m : ℤ) * ((m : ℤ) - 5) * ((m : ℤ) - 3) := by ring
    rw [h_eq]
    nlinarith

