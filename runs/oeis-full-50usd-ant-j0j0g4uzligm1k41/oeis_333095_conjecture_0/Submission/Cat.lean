import FormalConjectures.Util.ProblemImports
open Nat Finset PowerSeries

noncomputable section

def Cq : PowerSeries ℚ := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries

theorem Cq_coeff (n : ℕ) : (coeff n) Cq = (catalan n : ℚ) := by
  unfold Cq; rw [coeff_map]; simp [PowerSeries.catalanSeries_coeff]

theorem Cq_const : (constantCoeff) Cq = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Cq_coeff]; simp

theorem Cq_rel : Cq^2 * PowerSeries.X + 1 = Cq := by
  unfold Cq
  have h := PowerSeries.catalanSeries_sq_mul_X_add_one
  have := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) h
  simpa using this

-- recurrence at power series level:  X * Cq^r = Cq^(r-1) - Cq^(r-2) for r ≥ 2
theorem Cq_step (r : ℕ) : PowerSeries.X * Cq^(r+2) = Cq^(r+1) - Cq^r := by
  have h : Cq^2 * PowerSeries.X = Cq - 1 := by
    have := Cq_rel
    linear_combination this
  calc PowerSeries.X * Cq^(r+2) = (Cq^2 * PowerSeries.X) * Cq^r := by ring
    _ = (Cq - 1) * Cq^r := by rw [h]
    _ = Cq^(r+1) - Cq^r := by ring
