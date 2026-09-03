import Submission.ZeroPhaseRectangularVariance

/-! A conditional obstruction to a proposed uniform rectangular variance bound.
The finite sixth-power estimate is unconditional. Equality of limiting rough
number densities follows IF the variance-cube bound and the two limits exist.
No prime-number or rough-number asymptotic is assumed as an axiom. -/
namespace Erdos970.GapAverages
open Finset Real Filter
open scoped Topology

lemma roughCount_gap_sixth_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (n p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (C : ℝ)
    (hV : rowConditionalVariance P (p * n) p (zeroPhase P hP) ^ 3 ≤ C * (n : ℝ) ^ 4) :
    (roughCount P n - roughCount P (p * n) / p) ^ 6 ≤
      (p : ℝ) ^ 3 * (C * (n : ℝ) ^ 4) := by
  have hh := pow_le_pow_left₀ (sq_nonneg _)
    (roughCount_gap_square_le P hP n p hp hc) 3
  rw [← pow_mul, mul_pow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hV (by positivity))

/-- At n=p^2, V^3<=C*n^4 forces the sixth power of the logarithmically
normalized density gap to be at most C*(log p)^6/p. -/
theorem rough_density_gap_sixth_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (C : ℝ)
    (hV : rowConditionalVariance P (p ^ 3) p (zeroPhase P hP) ^ 3 ≤ C * (p : ℝ) ^ 8) :
    (log p / (p : ℝ) ^ 2 * roughCount P (p ^ 2) -
      log p / (p : ℝ) ^ 3 * roughCount P (p ^ 3)) ^ 6 ≤
      C * log p ^ 6 / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp0 := ne_of_gt hpR
  have hpn : p * p ^ 2 = p ^ 3 := by ring
  have hh := roughCount_gap_sixth_le P hP (p ^ 2) p hp hc C (by
    simpa only [hpn, Nat.cast_pow, ← pow_mul] using hV)
  rw [hpn, Nat.cast_pow] at hh
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ (log p / (p : ℝ) ^ 2) ^ 6 by positivity)
  convert hs using 1 <;> field_simp

lemma tendsto_log_sixth_div_nat :
    Tendsto (fun p : ℕ => log (p : ℝ) ^ 6 / p) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (6 : ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero
  simp only [rpow_ofNat, rpow_one] at hh
  exact hh.comp tendsto_natCast_atTop_atTop

/-- This is a necessary condition on any proposed uniform V^3<=C*n^4 bound.
In particular, distinct short and long density limits would refute that bound.
Both density limits are explicit hypotheses, not asserted here. -/
theorem rough_limits_eq_of_variance_cube_bound
    (p : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (hP : ∀ j, ∀ q ∈ P j, q.Prime) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, ∀ q ∈ P j, (p j).Coprime q)
    (hptop : Tendsto p atTop atTop) (C a b : ℝ)
    (hV : ∀ᶠ j in atTop,
      rowConditionalVariance (P j) (p j ^ 3) (p j) (zeroPhase (P j) (hP j)) ^ 3 ≤
        C * (p j : ℝ) ^ 8)
    (ha : Tendsto (fun j => log (p j : ℝ) / (p j : ℝ) ^ 2 * roughCount (P j) (p j ^ 2)) atTop (𝓝 a))
    (hb : Tendsto (fun j => log (p j : ℝ) / (p j : ℝ) ^ 3 * roughCount (P j) (p j ^ 3)) atTop (𝓝 b)) :
    a = b := by
  have hzero : Tendsto (fun j =>
      (log (p j : ℝ) / (p j : ℝ) ^ 2 * roughCount (P j) (p j ^ 2) -
        log (p j : ℝ) / (p j : ℝ) ^ 3 * roughCount (P j) (p j ^ 3)) ^ 6) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun j => by positivity))
    · filter_upwards [hV] with j hj
      exact rough_density_gap_sixth_le (P j) (hP j) (p j) (hp j) (hc j) C hj
    · have hh := (tendsto_log_sixth_div_nat.comp hptop).const_mul C
      simpa only [mul_zero, mul_div_assoc] using hh
  have heq : (a - b) ^ 6 = 0 := tendsto_nhds_unique ((ha.sub hb).pow 6) hzero
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero heq)

#print axioms rough_density_gap_sixth_le
#print axioms rough_limits_eq_of_variance_cube_bound
end Erdos970.GapAverages
