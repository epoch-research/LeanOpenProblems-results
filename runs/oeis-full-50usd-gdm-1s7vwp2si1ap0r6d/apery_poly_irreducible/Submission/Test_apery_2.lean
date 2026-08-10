import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma test_not_isSquare : ¬ IsSquare (5 / 6 : ℚ) := by
  norm_num

lemma apery_poly_2 : apery_poly 2 = 6 * X ^ 2 + 12 * X + 1 := by
  dsimp [apery_poly]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp [C_ofNat]
  have : (choose 4 2 : ℚ[X]) = 6 := rfl
  rw [this]
  ring

theorem apery_poly_irreducible_test (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) :=
  answer(sorry)
