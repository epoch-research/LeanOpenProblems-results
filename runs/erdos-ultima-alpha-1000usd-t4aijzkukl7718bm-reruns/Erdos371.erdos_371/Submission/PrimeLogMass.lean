import FormalConjecturesUtil
import Submission.LogSmoothCount

/-! An elementary bounded-error estimate for the logarithmically weighted
prime sum. This is a one-variable estimate; it does not establish joint
symmetry for largest prime factors of neighboring integers. -/

namespace Erdos371PrimeLogMass

open Finset Filter
open scoped Topology

noncomputable def mass (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, Real.log (p:ℝ)/(p:ℝ)

noncomputable def correctionBound : ℝ :=
  4 * ∑' n : ℕ, 1/(n:ℝ)^(3/2:ℝ)

lemma correctionBound_nonneg : 0 ≤ correctionBound := by
  unfold correctionBound
  positivity

lemma prime_correction_bound {p : ℕ} (hp : 2 ≤ p) :
    Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 4/(p:ℝ)^(3/2:ℝ) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hlog := Real.log_le_rpow_div (ε := (1/2:ℝ)) hp0.le (by norm_num)
  have hpow : (p:ℝ)^(1/2:ℝ)*(p:ℝ)^(3/2:ℝ) = (p:ℝ)^2 := by
    rw [← Real.rpow_add hp0]
    norm_num
  have hrpos := Real.rpow_pos_of_pos hp0 (3/2:ℝ)
  have hpred : (0:ℝ) < (p:ℝ)-1 := by linarith
  apply (div_le_div_iff₀ (by positivity : 0 < (p:ℝ)*((p:ℝ)-1)) hrpos).mpr
  have hh := mul_le_mul_of_nonneg_right hlog hrpos.le
  norm_num at hh
  nlinarith

lemma correction_sum_bound (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))) ≤
      correctionBound := by
  have hs : Summable (fun n : ℕ => 1/(n:ℝ)^(3/2:ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ p ∈ (N+1).primesBelow, 4/(p:ℝ)^(3/2:ℝ) := by
      apply sum_le_sum
      intro p hp
      exact prime_correction_bound (Nat.prime_of_mem_primesBelow hp).two_le
    _ = 4 * ∑ p ∈ (N+1).primesBelow, 1/(p:ℝ)^(3/2:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ correctionBound := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hs.sum_le_tsum _ (fun n _ => by positivity)

lemma factorial_log_lower {N : ℕ} (hN : 0 < N) :
    (N:ℝ)*Real.log N-N ≤ Real.log (N.factorial:ℝ) := by
  have hh := Stirling.le_log_factorial_stirling hN.ne'
  have hp : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hn := Real.log_natCast_nonneg N
  linarith

lemma factorial_log_upper (N : ℕ) :
    Real.log (N.factorial:ℝ) ≤ (N:ℝ)*(mass N+correctionBound) := by
  rw [Erdos371LogSmoothCount.log_factorial_prime_sum]
  calc
    _ ≤ ∑ p ∈ (N+1).primesBelow, (N:ℝ)/((p:ℝ)-1)*Real.log p := by
      apply sum_le_sum
      intro p hp
      have hprime := Nat.prime_of_mem_primesBelow hp
      have hf : (N.factorial.factorization p:ℝ) ≤ (N:ℝ)/((p:ℝ)-1) := by
        calc
          _ ≤ ((N/(p-1):ℕ):ℝ) := Nat.cast_le.mpr (Nat.factorization_factorial_le_div_pred hprime N)
          _ ≤ (N:ℝ)/(p-1:ℕ) := Nat.cast_div_le
          _ = _ := by rw [Nat.cast_sub hprime.one_le]; norm_num
      exact mul_le_mul_of_nonneg_right hf (Real.log_natCast_nonneg p)
    _ = (N:ℝ)*(mass N+
        ∑ p ∈ (N+1).primesBelow, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))) := by
      unfold mass
      rw [← sum_add_distrib, mul_sum]
      apply sum_congr rfl
      intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
      have hp0 : (p:ℝ) ≠ 0 := by linarith
      have hp1 : (p:ℝ)-1 ≠ 0 := by linarith
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (correction_sum_bound N)) (Nat.cast_nonneg N)

/-- A form of Mertens' first estimate, with a constant independent of the cutoff. -/
theorem mass_bounds {N : ℕ} (hN : 0 < N) :
    Real.log N-(1+correctionBound) ≤ mass N ∧ mass N ≤ Real.log N+Real.log 4 := by
  constructor
  · have hl := factorial_log_lower hN
    have hu := factorial_log_upper N
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hh : (N:ℝ)*(Real.log N-1-correctionBound) ≤ (N:ℝ)*mass N := by
      nlinarith
    have h := (mul_le_mul_iff_right₀ hn).mp hh
    linarith
  · exact Erdos371LogSmoothCount.prime_log_div_bound hN

/-- The logarithmically weighted prime mass has leading term `log N`. -/
theorem mass_log_ratio_tendsto_one :
    Tendsto (fun N : ℕ => mass N/Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun N : ℕ => 1-(1+correctionBound)/Real.log N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hlog.const_div_atTop (1+correctionBound))
  have hupp : Tendsto (fun N : ℕ => 1+Real.log 4/Real.log N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hlog.const_div_atTop (Real.log 4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hh := div_le_div_of_nonneg_right (mass_bounds (by omega : 0<N)).1 hl.le
    simpa [sub_div, hl.ne'] using hh
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hh := div_le_div_of_nonneg_right (mass_bounds (by omega : 0<N)).2 hl.le
    simpa [add_div, hl.ne'] using hh

end Erdos371PrimeLogMass

#print axioms Erdos371PrimeLogMass.mass_bounds
#print axioms Erdos371PrimeLogMass.mass_log_ratio_tendsto_one
