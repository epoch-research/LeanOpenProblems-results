import Submission.BuchstabPrimeTail

/-! Complete prime-summed tail estimates. Small primes are handled by an exact
wheel; the seventh logarithmic moment retains its explicit sixth-power error. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma scaled_excess_sum_le_moment (P : Finset ℕ) (R W : ℕ) (hR : 0 < R)
    (hP : P ⊆ (R+1).primesBelow) (L B : ℝ) (hB : 0 ≤ B)
    (hsmall : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp L)
    (hfar : ∀ p ∈ P, W < p → scaledPrimeExcess L p ≤ B*(log (p : ℝ)^7/p)) :
    (∑ p ∈ P, scaledPrimeExcess L p) ≤
      B*(log (R : ℝ)^7/7+2*WeightedMertens.sharpMomentError*log (R : ℝ)^6) := by
  have hpbound (p : ℕ) (hp : p ∈ P) : scaledPrimeExcess L p ≤ B*(log (p : ℝ)^7/p) := by
    by_cases hpW : p ≤ W
    · rw [scaledPrimeExcess_zero_on_wheel W p (WeightedMertens.mem_primes.mp (hP hp)).1 hpW L hsmall]
      exact mul_nonneg hB (div_nonneg (pow_nonneg (log_natCast_nonneg p) _) (Nat.cast_nonneg p))
    · exact hfar p hp (by omega)
  have hs := sum_le_sum hpbound
  rw [← mul_sum] at hs
  have hsub : (∑ p ∈ P, log (p : ℝ)^7/p) ≤
      ∑ p ∈ (R+1).primesBelow, log (p : ℝ)^7/p :=
    sum_le_sum_of_subset_of_nonneg hP (fun p _ _ =>
      div_nonneg (pow_nonneg (log_natCast_nonneg p) _) (Nat.cast_nonneg p))
  have hm := (abs_le.mp (WeightedMertens.prime_log_moment R hR 5)).2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hm
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ hB
  linarith only [hm,hsub]

theorem scaled_excess_sum_ninth_tail (P : Finset ℕ) (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (hP : P ⊆ (R+1).primesBelow) (L : ℝ) (hL : 0 < L) (hRL : 9*log (R : ℝ) ≤ L)
    (hsmall : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp L)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (W : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (W : ℝ)) :
    (∑ p ∈ P, scaledPrimeExcess L p) ≤ (6*9^8/(217*L^8))*
      (log (R : ℝ)^7/7+2*WeightedMertens.sharpMomentError*log (R : ℝ)^6) := by
  apply scaled_excess_sum_le_moment P R W hR hP L _ (by positivity) hsmall
  intro p hp hpW
  obtain ⟨hpp,hpR⟩ := WeightedMertens.mem_primes.mp (hP hp)
  have hlogR : log (p : ℝ) ≤ log (R : ℝ) := log_le_log
    (by exact_mod_cast hpp.pos) (by exact_mod_cast hpR)
  have hlogW : log (W : ℝ) ≤ log (p : ℝ) := log_le_log
    (by exact_mod_cast hW) (by exact_mod_cast hpW.le)
  exact scaledPrimeExcess_le_ninth_tail p hpp L hL (by linarith)
    (hthreshold.trans hlogW) (hthreshold'.trans hlogW)

theorem scaled_excess_sum_thirteenth_tail (P : Finset ℕ) (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (hP : P ⊆ (R+1).primesBelow) (L : ℝ) (hL : 0 < L) (hRL : 13*log (R : ℝ) ≤ L)
    (hsmall : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp L)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (W : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (W : ℝ)) :
    (∑ p ∈ P, scaledPrimeExcess L p) ≤ (6*(26/3 : ℝ)^8/(217*L^8))*
      (log (R : ℝ)^7/7+2*WeightedMertens.sharpMomentError*log (R : ℝ)^6) := by
  apply scaled_excess_sum_le_moment P R W hR hP L _ (by positivity) hsmall
  intro p hp hpW
  obtain ⟨hpp,hpR⟩ := WeightedMertens.mem_primes.mp (hP hp)
  have hlogR : log (p : ℝ) ≤ log (R : ℝ) := log_le_log
    (by exact_mod_cast hpp.pos) (by exact_mod_cast hpR)
  have hlogW : log (W : ℝ) ≤ log (p : ℝ) := log_le_log
    (by exact_mod_cast hW) (by exact_mod_cast hpW.le)
  exact scaledPrimeExcess_le_thirteenth_tail p hpp L hL (by linarith)
    (hthreshold.trans hlogW) (hthreshold'.trans hlogW)

#print axioms scaled_excess_sum_ninth_tail
#print axioms scaled_excess_sum_thirteenth_tail
end Erdos970.FiniteSelberg
