import Submission.BinaryCriticalJordanSlope
import Submission.BinaryCriticalMinObserver

/-! Necessary products of slope ratios on cycles of residue phases.
These are obstructions to certificate models, not Erdős 406 itself. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped BigOperators

lemma ratio_path_bound (x c : ℕ → ℝ) (L : ℕ)
    (hc : ∀ n < L, 0 ≤ c n)
    (hstep : ∀ n < L, x (n+1) ≤ c n*x n) :
    x L ≤ (∏ n ∈ Finset.range L, c n)*x 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hh := ih (fun n hn => hc n (by omega)) (fun n hn => hstep n (by omega))
    have hm := mul_le_mul_of_nonneg_left hh (hc L (by omega))
    have hs := hstep L (by omega)
    rw [Finset.prod_range_succ]
    nlinarith

/-- Positive leading coefficients cannot return to themselves along a cycle
whose product of allowed ratios is strictly less than one. -/
theorem phase_cycle_slope_product (x c : ℕ → ℝ) (L : ℕ)
    (hx : 0 < x 0) (hreturn : x L=x 0)
    (hc : ∀ n < L, 0 ≤ c n)
    (hstep : ∀ n < L, x (n+1) ≤ c n*x n) :
    1 ≤ ∏ n ∈ Finset.range L, c n := by
  have h := ratio_path_bound x c L hc hstep
  rw [hreturn] at h
  exact (mul_le_mul_iff_left₀ hx).mp (by simpa [mul_comm] using h)

/-- Different phases may have different observer families and different
minimum leading coefficients. A single edge compares their minima. -/
theorem minimum_phase_slope_edge {ι τ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype τ] [Nonempty τ]
    (x : ι → ℝ) (y : τ → ℝ) (a c B : ℝ) (ha : 0 ≤ a)
    (F : ι → ℕ → ℝ) (G : τ → ℕ → ℝ) (C : ι → ℝ)
    (hG : ∀ i n, a*y i*n-B ≤ G i n)
    (hF : ∀ j n, F j n ≤ c*x j*n+C j)
    (hmatch : ∀ n j, ∃ i, G i n ≤ F j n) :
    a*Erdos406BinaryCriticalMinObserver.minValue y ≤
      c*Erdos406BinaryCriticalMinObserver.minValue x := by
  obtain ⟨j,hj⟩ := Erdos406BinaryCriticalMinObserver.minValue_attained x
  apply affine_slope_le _ B _ (C j)
  intro n
  obtain ⟨i,hi⟩ := hmatch n j
  have hmin := Erdos406BinaryCriticalMinObserver.minValue_le y i
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin ha)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hg := hG i n
  have hf := hF j n
  rw [hj]
  linarith

#print axioms ratio_path_bound
#print axioms phase_cycle_slope_product
#print axioms minimum_phase_slope_edge
end Erdos406BinaryCriticalRecurrence
