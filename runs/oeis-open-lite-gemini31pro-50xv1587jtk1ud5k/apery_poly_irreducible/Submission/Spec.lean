import FormalConjectures.Util.ProblemImports

open Nat Polynomial

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_1 : apery_poly 1 = C (2:ℚ) * X + C (1:ℚ) := by
  rw [apery_poly]
  simp [Finset.sum_range_succ]
  change 1 + 2 * X = C 2 * X + 1
  rw [map_ofNat]
  ring

theorem irreducible_apery_poly_1 : Irreducible (apery_poly 1) := by
  rw [apery_poly_1]
  apply irreducible_of_degree_eq_one
  rw [degree_add_C]
  · exact degree_C_mul_X (by decide)
  · rw [degree_C_mul_X (by decide)]
    exact WithBot.coe_lt_coe.mpr (by decide)

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  sorry

theorem apery_poly_irreducible.disproof : ¬ (∀ n : ℕ, 1 ≤ n → Irreducible (apery_poly n)) := by
  sorry
