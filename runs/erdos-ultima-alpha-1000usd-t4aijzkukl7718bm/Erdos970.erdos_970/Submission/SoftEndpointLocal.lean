import Submission.SoftEndpointDerivative

/-! Strict initial improvement at every non-periodic interval length.
The positive neighborhood depends on the prime set and interval length;
no uniform positive Laplace parameter is obtained. -/
namespace Erdos970.GapAverages
open Finset Real Filter
open scoped Topology

/-- The full-divisor term alone gives a quantitative positive slope whenever
the interval length is not a multiple of the full prime product. -/
theorem endpointSlope_ge_remainder (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    ((m % (∏ p ∈ P, p) : ℕ) : ℝ)/(∏ p ∈ P, (p : ℝ))^2 ≤
      endpointSlope P m := by
  have hN : 0 < ∏ p ∈ P, p := prod_pos (fun p hp => (hP p hp).pos)
  have hNR : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hN
  have he : (m : ℝ)/(∏ p ∈ P, (p : ℝ)) - (m/(∏ p ∈ P, p) : ℕ) =
      ((m % (∏ p ∈ P, p) : ℕ) : ℝ)/(∏ p ∈ P, (p : ℝ)) := by
    have hh : ((m % (∏ p ∈ P, p) : ℕ) : ℝ) +
        (∏ p ∈ P, (p : ℝ))*(m/(∏ p ∈ P, p) : ℕ) = m := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.mod_add_div m (∏ p ∈ P, p)
    field_simp
    nlinarith only [hh]
  have hw : pairWeight P P = 1/(∏ p ∈ P, (p : ℝ)) := by
    simp [pairWeight, one_div, prod_inv_distrib]
  rw [endpointSlope_expansion P hP]
  have hs := single_le_sum (s := P.powerset)
    (f := fun Q => pairWeight P Q *
      ((m : ℝ)/(∏ p ∈ Q, (p : ℝ)) - (m/(∏ p ∈ Q, p) : ℕ)))
    (fun Q hQ => mul_nonneg (pairWeight_nonneg P Q hP) (by
      apply sub_nonneg.mpr
      simpa only [Nat.cast_prod] using
        (Nat.cast_div_le (α := ℝ) (m := m) (n := ∏ p ∈ Q, p))))
    (mem_powerset.mpr (Subset.refl P))
  dsimp only at hs
  rw [hw, he] at hs
  convert hs using 1
  ring

/-- Exactly the complete-period lengths have zero initial slope. -/
theorem endpointSlope_eq_zero_iff (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    endpointSlope P m = 0 ↔ (∏ p ∈ P, p) ∣ m := by
  constructor
  · intro hz
    have hh := endpointSlope_ge_remainder P hP m
    rw [hz] at hh
    have hN : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) :=
      prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
    have hr : ((m % (∏ p ∈ P, p) : ℕ) : ℝ) ≤ 0 := by
      have ht := (div_le_iff₀ (sq_pos_of_pos hN)).mp hh
      simpa only [zero_mul] using ht
    have hzmod : m % (∏ p ∈ P, p) = 0 := by exact_mod_cast (le_antisymm hr (by positivity))
    exact Nat.dvd_of_mod_eq_zero hzmod
  · intro hm
    rw [endpointSlope_expansion P hP]
    apply sum_eq_zero
    intro Q hQ
    have hd := (prod_dvd_prod_of_subset Q P id (mem_powerset.mp hQ)).trans hm
    simp only [id_eq] at hd
    have hpos : (0 : ℝ) < (∏ p ∈ Q, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hP p ((mem_powerset.mp hQ) hp)).pos)
    rw [Nat.cast_div hd hpos.ne']
    simp only [Nat.cast_prod, sub_self, mul_zero]

/-- A genuine local conclusion for each fixed prime set and interval length.
The quantifiers do not allow choosing one positive parameter for all P,m. -/
theorem eventually_tiltedEndpoint_gt_density (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (hm : ¬(∏ p ∈ P, p) ∣ m) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, density P < tiltedEndpoint P m t := by
  have hs : 0 < endpointSlope P m := by
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (endpointSlope_nonneg P hP m)
    exact hm ((endpointSlope_eq_zero_iff P hP m).mp hz)
  have he := (hasDerivAt_tiltedEndpoint_zero P hP m).tendsto_slope_zero_right.eventually
    (lt_mem_nhds hs)
  filter_upwards [he, self_mem_nhdsWithin] with t ht htp
  have htpos : 0 < t := htp
  simp only [zero_add, smul_eq_mul, tiltedEndpoint_zero P hP m] at ht
  have hd := (mul_pos_iff_of_pos_left (inv_pos.mpr htpos)).mp ht
  exact sub_pos.mp hd

#print axioms endpointSlope_ge_remainder
#print axioms endpointSlope_eq_zero_iff
#print axioms eventually_tiltedEndpoint_gt_density
end Erdos970.GapAverages
