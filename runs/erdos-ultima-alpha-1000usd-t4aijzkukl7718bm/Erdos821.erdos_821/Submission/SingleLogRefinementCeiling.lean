import Submission.CutoffRefinementBudget

/-!
# Refining the finite-local parametric supplies does not cross their limit

This concerns the density `1/(12*C)` supplied by the proved single-log
conversion. It does not rule out a stronger density estimate or other
arithmetic methods.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 2000000

/-- Even the unrestricted prime count forces a linear lower bound on the
constant in any single-log smooth-prime count at this exponential scale. -/
lemma single_log_count_constant_lower (t b C : ℕ) (ht : 1 ≤ t) (hC : 0 < C)
    (H : ∀ᶠ m : ℕ in atTop, (independentN t m : ℝ)  ≤  (C : ℝ)*m*
      ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) :
    (t : ℝ)  ≤  4*(C : ℝ) := by
  have hpib := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (progressionScaleN_mul_tendsto t ht)).eventually
      (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  obtain ⟨m,hm,hpi,hm1⟩ := (H.and (hpib.and (eventually_ge_atTop 1))).exists
  let N := independentN t m
  let Y := independentN b m
  have hN : (0 : ℝ) < N := by dsimp [N,independentN]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : (t : ℝ)*m  ≤  Real.log N := by
    simpa only [N,independentN,progressionScaleN,mul_assoc,Nat.cast_mul] using log_progression_scale_ge (t*m)
  have hlog0 : 0 < Real.log N := (mul_pos htR hmR).trans_le hlog
  have hpi' : (N.primeCounting : ℝ)  ≤  (Real.log 4+1)*(N : ℝ)/Real.log N := by
    simpa only [Function.comp_apply,Nat.floor_natCast,N,independentN,progressionScaleN,mul_assoc] using hpi
  have hfour : Real.log (4 : ℝ)+1  ≤  4 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have hcard : ((smoothPrimePool N Y).card : ℝ)  ≤  (N.primeCounting : ℝ) := by
    apply Nat.cast_le.mpr
    simpa only [smoothPrimePool,Nat.primeCounting,← Nat.primesBelow_card_eq_primeCounting'] using
      (card_filter_le (s := (N+1).primesBelow) (p := fun p => p-1 ∈ Nat.smoothNumbers Y))
  have hbound : ((smoothPrimePool N Y).card : ℝ)  ≤  4*(N : ℝ)/Real.log N :=
    hcard.trans (hpi'.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfour hN.le) hlog0.le))
  have hall : (N : ℝ)  ≤  (C : ℝ)*m*(4*(N : ℝ)/Real.log N) :=
    hm.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
  have hall' := mul_le_mul_of_nonneg_right hall hlog0.le
  have he : ((C : ℝ)*m*(4*(N : ℝ)/Real.log N))*Real.log N =
      (4*(C : ℝ)*m)*(N : ℝ) := by field_simp
  rw [he] at hall'
  have hlogup : Real.log N  ≤  4*(C : ℝ)*m := by
    apply (mul_le_mul_iff_right₀ hN).mp
    simpa only [mul_comm] using hall'
  exact (mul_le_mul_iff_left₀ hmR).mp (hlog.trans hlogup)

namespace CutoffRefinementBudget

/-- A gap of one scale unit is larger than the entire density budget
produced by the existing count-to-weight conversion. -/
lemma converted_density_floor_gt (β η t C : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ht : 0 < t) (hC : 0 < C) (htC : t ≤ 4*C) (hgap : η ≤ β-1/t) :
    η  <  β*Real.exp (-(1/(12*C))) := by
  have hsmall : 1/(12*C) < 1/t := by
    apply one_div_lt_one_div_of_lt ht
    linarith only [htC,hC]
  have hc : 0 ≤ 1/(12*C) := by positivity
  have hexp := Real.add_one_le_exp (-(1/(12*C)))
  have hexpmul := mul_le_mul_of_nonneg_left hexp hβ.le
  have hprod := mul_le_mul_of_nonneg_right hβ1 hc
  nlinarith only [hgap,hsmall,hexpmul,hprod]

/-- A consequence for all chains satisfying the charged refinement rule. -/
theorem converted_count_chain_above (β c : ℕ → ℝ) (hβ : ∀ i, 0 < β i)
    (hβ1 : β 0 ≤ 1) (hc : ∀ i, 0 ≤ c i)
    (hstep : ∀ i, Real.log (β i/β (i+1))  ≤  c i-c (i+1))
    (t b C : ℕ) (ht : 1 ≤ t) (hC : 0 < C) (η : ℝ) (hgap : η ≤ β 0-1/(t : ℝ))
    (hc0 : c 0=1/(12*(C : ℝ)))
    (H : ∀ᶠ m : ℕ in atTop, (independentN t m : ℝ)  ≤  (C : ℝ)*m*
      ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) (n : ℕ) :
    η  <  β n := by
  have hf := converted_density_floor_gt (β 0) η t C (hβ 0) hβ1
    (by exact_mod_cast ht) (by exact_mod_cast hC) (single_log_count_constant_lower t b C ht hC H) hgap
  have hb := cutoff_lower_bound β c hβ hc hstep n
  rw [hc0] at hb
  exact hf.trans_le hb

end CutoffRefinementBudget

lemma finite_local_parametric_ratio_gap (N M k : ℕ) (hN : 1 ≤ N) :
    (N : ℝ)/(2*(N : ℝ)+M)  ≤ 
      ((4*N*k+21 : ℕ) : ℝ)/((4*(2*N+M)*k+20 : ℕ) : ℝ)-
        1/((4*(2*N+M)*k+20 : ℕ) : ℝ) := by
  have hA : (0 : ℝ) < 2*(N : ℝ)+M := by positivity
  have ht : (0 : ℝ) < ((4*(2*N+M)*k+20 : ℕ) : ℝ) := by positivity
  rw [← sub_div]
  apply (div_le_div_iff₀ hA ht).mpr
  push_cast
  nlinarith only [Nat.cast_nonneg (α := ℝ) N,Nat.cast_nonneg (α := ℝ) M]

lemma finite_local_parametric_ratio_ge_limit (D : ℕ) (hD : 2 ≤ D) :
    (2048/4351 : ℝ)  ≤  ((2048*D : ℕ) : ℝ)/
      (2*((2048*D : ℕ) : ℝ)+(255*(D-1) : ℕ)) := by
  have hpos : (0 : ℝ) < 2*((2048*D : ℕ) : ℝ)+(255*(D-1) : ℕ) := by positivity
  apply (le_div_iff₀ hpos).mpr
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1 ≤ D by omega),Nat.cast_one]
  linarith

/-- Applying the charged iteration with the density supplied by the existing
conversion to a finite-local parametric count stays strictly above 2048/4351.
This is not a lower bound on the actual smoothness ratios that primes attain. -/
theorem finite_local_converted_refinement_above_limit (D k C : ℕ) (hD : 2 ≤ D) (hk : 1 ≤ k)
    (hC : 0 < C) (β c : ℕ → ℝ) (hβ : ∀ i, 0 < β i) (hc : ∀ i, 0 ≤ c i)
    (hstep : ∀ i, Real.log (β i/β (i+1))  ≤  c i-c (i+1))
    (hc0 : c 0=1/(12*(C : ℝ)))
    (hβ0 : β 0=((4*(2048*D)*k+21 : ℕ) : ℝ)/
      ((4*(2*(2048*D)+255*(D-1))*k+20 : ℕ) : ℝ))
    (H : ∀ᶠ m : ℕ in atTop,
      (independentN (4*(2*(2048*D)+255*(D-1))*k+20) m : ℝ)  ≤  (C : ℝ)*m*
        ((smoothPrimePool (independentN (4*(2*(2048*D)+255*(D-1))*k+20) m)
          (independentN (4*(2048*D)*k+21) m)).card : ℝ)) (n : ℕ) :
    (2048/4351 : ℝ) < β n := by
  apply CutoffRefinementBudget.converted_count_chain_above β c hβ _ hc hstep
    (4*(2*(2048*D)+255*(D-1))*k+20) (4*(2048*D)*k+21) C (by omega) hC
    (2048/4351) _ hc0 H n
  · rw [hβ0]
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (show 4*(2048*D)*k+21  ≤  4*(2*(2048*D)+255*(D-1))*k+20 by
      have hNk := Nat.le_mul_of_pos_right (2048*D) hk
      nlinarith only [hNk,hD,Nat.zero_le (255*(D-1)*k)])
  · rw [hβ0]
    exact (finite_local_parametric_ratio_ge_limit D hD).trans
      (finite_local_parametric_ratio_gap (2048*D) (255*(D-1)) k (by omega))

end Erdos821
