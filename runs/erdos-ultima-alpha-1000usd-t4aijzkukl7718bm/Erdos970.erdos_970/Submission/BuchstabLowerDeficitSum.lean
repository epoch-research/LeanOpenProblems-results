import Submission.BuchstabDeficitTail

/-! Summed small-prime lower-child deficit, including the fixed wheel and the
explicit moment remainder. The enlarged terminal integral budget is charged. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg

noncomputable def LowerTailValid (N : ℕ) : Prop := ∀ k : ℕ, N ≤ nthPrime k →
  ∀ v : ℝ, 9 ≤ v → prefixDensity primeMarginal k*(1-(4/525 : ℝ)*(9/v)^8) ≤
    referenceLower 0 k (exp (v*log (nthPrime k : ℝ)))

lemma exists_lowerTailValid : ∃ N : ℕ, LowerTailValid N := exists_referenceLower_zero_tail

lemma prime_function_sum_le_moment (P : Finset ℕ) (R : ℕ) (hR : 0 < R)
    (hP : P ⊆ (R+1).primesBelow) (f : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ p ∈ P, f p ≤ B*(log (p : ℝ)^7/p)) :
    (∑ p ∈ P, f p) ≤ B*(log (R : ℝ)^7/7+2*WeightedMertens.sharpMomentError*log (R : ℝ)^6) := by
  have hs := sum_le_sum hbound
  rw [← mul_sum] at hs
  have hsub : (∑ p ∈ P, log (p : ℝ)^7/p) ≤ ∑ p ∈ (R+1).primesBelow, log (p : ℝ)^7/p :=
    sum_le_sum_of_subset_of_nonneg hP (fun p _ _ =>
      div_nonneg (pow_nonneg (log_natCast_nonneg p) _) (Nat.cast_nonneg p))
  have hm := (abs_le.mp (WeightedMertens.prime_log_moment R hR 5)).2
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hm
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ hB
  linarith only [hsub,hm]

lemma lower_deficit_sum_le_moment (P : Finset ℕ) (R W N : ℕ) (hR : 0 < R) (hW : 0 < W)
    (hP : P ⊆ (R+1).primesBelow) (hNW : N ≤ W) (hN : LowerTailValid N)
    (L : ℝ) (hL : 0 < L) (hRL : 13*log (R : ℝ) ≤ L)
    (hsmall1 : (W : ℝ)^3 ≤ exp L)
    (hsmall2 : (W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ exp L)
    (hthreshold : supportMassLogThreshold ≤ log (W : ℝ)) :
    (∑ p ∈ P, primeLowerDeficit L p) ≤ (lowerTailCoefficient/L^8)*
      (log (R : ℝ)^7/7+2*WeightedMertens.sharpMomentError*log (R : ℝ)^6) := by
  apply prime_function_sum_le_moment P R hR hP _ _
    (div_nonneg lowerTailCoefficient_nonneg (pow_nonneg hL.le _))
  intro p hp
  obtain ⟨hpp,hpR⟩ := WeightedMertens.mem_primes.mp (hP hp)
  by_cases hpW : p ≤ W
  · rw [primeLowerDeficit_zero_on_wheel W p hpp hpW L hsmall1 hsmall2]
    exact mul_nonneg (div_nonneg lowerTailCoefficient_nonneg (pow_nonneg hL.le _))
      (div_nonneg (pow_nonneg (log_natCast_nonneg p) _) (Nat.cast_nonneg p))
  · have hWp : W ≤ p := by omega
    have hlogW : log (W : ℝ) ≤ log (p : ℝ) := log_le_log
      (by exact_mod_cast hW) (by exact_mod_cast hWp)
    have hlogR : log (p : ℝ) ≤ log (R : ℝ) := log_le_log
      (by exact_mod_cast hpp.pos) (by exact_mod_cast hpR)
    apply primeLowerDeficit_le_thirteenth p hpp L hL (by linarith) (hthreshold.trans hlogW)
    intro v hv
    have hh := hN (primeIndex p) (by simpa only [nthPrime_primeIndex p hpp] using hNW.trans hWp) v hv
    simpa only [density_primeIndex p hpp,nthPrime_primeIndex p hpp] using hh

theorem reference_lower_deficit_tail_finite (k W N : ℕ) (hW : 0 < W)
    (hNW : N ≤ W) (hN : LowerTailValid N)
    (hthreshold : supportMassLogThreshold ≤ log (W : ℝ))
    (hRW : W^3+W^2*(firstHitWheel W)^2 ≤ nthPrime k)
    (hlarge : 20*truncatedTailError lowerTailCoefficient ≤ lowerGridTail*log (nthPrime k : ℝ))
    (hEuler : eulerMass (nthPrime k+1).primesBelow ≤ (9/5 : ℝ)*log (nthPrime k : ℝ))
    (s : ℝ) (hs : 1 ≤ s) :
    eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ smallPrimePart k (s*log (nthPrime k : ℝ)), primeLowerDeficit (s*log (nthPrime k : ℝ)) p) ≤
        lowerGridTail/s := by
  let L := log (nthPrime k : ℝ)
  let R := tailPrimeCut (s*L)
  have hp : (nthPrime k).Prime := nthPrime_prime k
  have hlog : 0 < L := log_pos (by exact_mod_cast hp.one_lt)
  have hs0 : 0 < s := by linarith
  have hτ : 0 < s*L := mul_pos hs0 hlog
  have hR : 0 < R := tailPrimeCut_pos _ hτ.le
  have hRL : 13*log (R : ℝ) ≤ s*L := by
    have hh := tailPrimeCut_log_le (s*L) hτ.le
    change log (R : ℝ) ≤ (s*L)/13 at hh
    linarith
  have hsmall : (W : ℝ)^3+(W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hWR : (W : ℝ)^3+(W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ nthPrime k := by exact_mod_cast hRW
    have hRexp : (nthPrime k : ℝ) ≤ exp (s*L) := by
      rw [← exp_log (show (0 : ℝ) < nthPrime k by exact_mod_cast hp.pos)]
      apply exp_le_exp.mpr
      change L ≤ s*L
      nlinarith
    exact hWR.trans hRexp
  have hsmall1 : (W : ℝ)^3 ≤ exp (s*L) := by
    have hz : (0 : ℝ) ≤ (W : ℝ)^2*(firstHitWheel W : ℝ)^2 := by positivity
    linarith
  have hsmall2 : (W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hz : (0 : ℝ) ≤ (W : ℝ)^3 := by positivity
    linarith
  have hsum := lower_deficit_sum_le_moment (smallPrimePart k (s*L)) R W N hR hW
    (smallPrimePart_subset_cut k (s*L)) hNW hN (s*L) hτ hRL hsmall1 hsmall2 hthreshold
  exact normalized_truncated_moment_le _ (eulerMass (nthPrime k).primesBelow) L s
    (log (R : ℝ)) lowerTailCoefficient lowerGridTail hsum
      (eulerMass_pos _ (fun p hp' => (Nat.mem_primesBelow.mp hp').2)).le
      ((eulerMass_strict_prefix_le _ hp).trans hEuler) hlog hs (log_natCast_nonneg R) hRL
      lowerTailCoefficient_nonneg lowerGridTail_pos.le lower_tail_main_budget hlarge

/-- A single absolute threshold handles the lower-deficit tail uniformly in
all parent divisor exponents s>=1. -/
theorem exists_reference_lower_deficit_tail : ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k →
    ∀ s : ℝ, 1 ≤ s → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ smallPrimePart k (s*log (nthPrime k : ℝ)), primeLowerDeficit (s*log (nthPrime k : ℝ)) p) ≤
        lowerGridTail/s := by
  obtain ⟨N,hN⟩ := exists_lowerTailValid
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨W,hW,hNW,hWlog⟩ := ((eventually_ge_atTop 1).and
    ((eventually_ge_atTop N).and (hlog.eventually_ge_atTop supportMassLogThreshold))).exists
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (W^3+W^2*(firstHitWheel W)^2)).and
      ((hlog.eventually_ge_atTop (20*truncatedTailError lowerTailCoefficient/lowerGridTail)).and
        eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨M,fun k hk s hs => ?_⟩
  obtain ⟨hRW,hRlog,hEuler⟩ := hM (nthPrime k) hk
  have hlarge : 20*truncatedTailError lowerTailCoefficient ≤ lowerGridTail*log (nthPrime k : ℝ) := by
    have hh := (div_le_iff₀ lowerGridTail_pos).mp hRlog
    nlinarith only [hh]
  exact reference_lower_deficit_tail_finite k W N (by omega) hNW hN hWlog hRW hlarge hEuler s hs

#print axioms reference_lower_deficit_tail_finite
#print axioms exists_reference_lower_deficit_tail
end Erdos970.RecursiveSieve.Buchstab
