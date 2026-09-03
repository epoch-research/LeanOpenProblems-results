import Submission.BuchstabTailMoments
import Submission.BuchstabDefectCoordinates

/-! A uniform polynomial tail for the first lower Buchstab main term.
The fixed initial wheel is exact, and the explicit Mertens-moment remainder
is absorbed only above a stated absolute threshold. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg

noncomputable def referenceUpper (n k : ℕ) (D : ℝ) : ℝ :=
  upperMain primeMarginal (primeKeep nthPrime) (scaledSelbergBase nthPrime) n k D
noncomputable def referenceLower (n k : ℕ) (D : ℝ) : ℝ :=
  lowerStep primeMarginal (primeKeep nthPrime) (referenceUpper n) k D

lemma referenceLower_nonneg (n k : ℕ) (D : ℝ) : 0 ≤ referenceLower n k D := lowerStep_nonneg _ _ _ _ _

lemma reference_density_bounds (n k : ℕ) (D : ℝ) :
    referenceLower n k D ≤ prefixDensity primeMarginal k ∧
      prefixDensity primeMarginal k ≤ referenceUpper n k D :=
  main_density_bounds _ (fun i => ⟨(primeMarginal_pos i).le,(primeMarginal_lt_one i).le⟩)
    _ _ (scaledSelbergBase_density nthPrime nthPrime_prime) n k D

lemma referenceUpper_antitone (n k : ℕ) : Antitone (referenceUpper n k) :=
  upperMain_level_antitone _ (fun i => (primeMarginal_pos i).le) _
    (fun k D E hDE hk => hk.trans hDE) _ (scaledSelbergBase_antitone nthPrime nthPrime_prime) n k

lemma referenceLower_monotone (n k : ℕ) : Monotone (referenceLower n k) :=
  lowerStep_level_monotone _ (fun i => (primeMarginal_pos i).le) _
    (fun k D E hDE hk => hk.trans hDE) _ (referenceUpper_antitone n) k

lemma reference_zero_excess_sum (k : ℕ) (L : ℝ) :
    (∑ i : Fin k, primeMarginal i.val*(referenceUpper 0 i.val (exp L*primeMarginal i.val)-
      prefixDensity primeMarginal i.val)) =
      ∑ p ∈ (nthPrime k).primesBelow, scaledPrimeExcess L p := by
  have hh := nthPrime_prefix_sum (scaledPrimeExcess L) k
  rw [← hh]
  apply sum_congr rfl
  intro i hi
  exact (scaledPrimeExcess_eq_indexed i.val L).symm

/-- An explicit finite form of the uniform lower-tail estimate. -/
theorem referenceLower_zero_tail_finite (k W : ℕ) (hW : 0 < W)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (W : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (W : ℝ))
    (hRW : W*(firstHitWheel W)^2 ≤ nthPrime k)
    (hlog : 280*WeightedMertens.sharpMomentError ≤ log (nthPrime k : ℝ))
    (hEuler : eulerMass (nthPrime k+1).primesBelow ≤ (9/5 : ℝ)*log (nthPrime k : ℝ))
    (s : ℝ) (hs : 9 ≤ s) :
    prefixDensity primeMarginal k*(1-(4/525 : ℝ)*(9/s)^8) ≤
      referenceLower 0 k (exp (s*log (nthPrime k : ℝ))) := by
  let R := nthPrime k
  let L := log (R : ℝ)
  let E := eulerMass R.primesBelow
  let S := ∑ p ∈ R.primesBelow, scaledPrimeExcess (s*L) p
  have hp : R.Prime := nthPrime_prime k
  have hR : (0 : ℝ) < R := by exact_mod_cast hp.pos
  have hL : 0 < L := log_pos (by exact_mod_cast hp.one_lt)
  have hs0 : 0 < s := by linarith
  have hτ : 0 < s*L := mul_pos hs0 hL
  have hP : R.primesBelow ⊆ (R+1).primesBelow := by
    intro p hp'
    obtain ⟨hpR,hpp⟩ := Nat.mem_primesBelow.mp hp'
    exact WeightedMertens.mem_primes.mpr ⟨hpp,hpR.le⟩
  have hsmall : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hWR : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ R := by exact_mod_cast hRW
    have hRe : (R : ℝ) ≤ exp (s*L) := by
      rw [← exp_log hR]
      apply exp_le_exp.mpr
      change L ≤ s*L
      nlinarith
    exact hWR.trans hRe
  have hsum := scaled_excess_sum_ninth_tail R.primesBelow R W hp.pos hW hP (s*L) hτ
    (by change 9*L ≤ s*L; nlinarith) hsmall hthreshold hthreshold'
  change S ≤ (6*9^8/(217*(s*L)^8))*(L^7/7+2*WeightedMertens.sharpMomentError*L^6) at hsum
  let B := (6*9^8/(217*(s*L)^8))*(L^7/7+2*WeightedMertens.sharpMomentError*L^6)
  have hB : 0 ≤ B := by
    dsimp [B]
    have hE := WeightedMertens.sharpMomentError_pos
    positivity
  have hE : 0 < E := eulerMass_pos _ (fun p hp' => (Nat.mem_primesBelow.mp hp').2)
  have hEu : E ≤ (9/5 : ℝ)*L := (eulerMass_strict_prefix_le R hp).trans hEuler
  have herr : 1/7+2*WeightedMertens.sharpMomentError/L ≤ (3/20 : ℝ) := by
    have he : 2*WeightedMertens.sharpMomentError/L ≤ (1/140 : ℝ) := by
      apply (div_le_iff₀ hL).mpr
      change 280*WeightedMertens.sharpMomentError ≤ L at hlog
      linarith
    linarith
  have halg : ((9/5 : ℝ)*L)*B = (54/(5*217) : ℝ)*(9/s)^8*
      (1/7+2*WeightedMertens.sharpMomentError/L) := by
    dsimp [B]
    field_simp
    <;> ring
  have hnorm : E*S ≤ (4/525 : ℝ)*(9/s)^8 := by
    calc
      E*S ≤ E*B := mul_le_mul_of_nonneg_left hsum hE.le
      _ ≤ ((9/5 : ℝ)*L)*B := mul_le_mul_of_nonneg_right hEu hB
      _ = _ := halg
      _ ≤ (54/(5*217) : ℝ)*(9/s)^8*(3/20) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ ≤ (4/525 : ℝ)*(9/s)^8 := by
        have ht : (0 : ℝ) ≤ (9/s)^8 := by positivity
        nlinarith
  have hS : S ≤ prefixDensity primeMarginal k*((4/525 : ℝ)*(9/s)^8) := by
    rw [nthPrime_prefix_density]
    change S ≤ (1/E)*((4/525 : ℝ)*(9/s)^8)
    have hh : S ≤ ((4/525 : ℝ)*(9/s)^8)/E :=
      (le_div_iff₀ hE).mpr (by simpa only [mul_comm S E] using hnorm)
    convert hh using 1 <;> ring
  have hkeep : primeKeep nthPrime k (exp (s*L)) := by
    change (R : ℝ)^2 ≤ exp (s*L)
    rw [← exp_log (pow_pos hR 2), log_pow]
    apply exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    change 2*L ≤ s*L
    nlinarith
  apply lowerStep_ge_of_excess primeMarginal (primeKeep nthPrime) (referenceUpper 0)
    k (exp (s*L)) (1-(4/525 : ℝ)*(9/s)^8) hkeep
  rw [reference_zero_excess_sum]
  change S ≤ _
  convert hS using 1 <;> ring

/-- The tail estimate is uniform for EVERY real divisor exponent s>=9.
Only the initial prime cutoff, not s, depends on the absolute threshold. -/
theorem exists_referenceLower_zero_tail : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ s : ℝ, 9 ≤ s → prefixDensity primeMarginal k*(1-(4/525 : ℝ)*(9/s)^8) ≤
      referenceLower 0 k (exp (s*log (nthPrime k : ℝ))) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨W,hW,hW1,hW2⟩ := ((eventually_ge_atTop 1).and
    ((hlog.eventually_ge_atTop (50*WeightedMertens.sharpMomentError)).and
      (hlog.eventually_ge_atTop supportMassLogThreshold))).exists
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (W*(firstHitWheel W)^2)).and
    ((hlog.eventually_ge_atTop (280*WeightedMertens.sharpMomentError)).and
      eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun k hk s hs => ?_⟩
  obtain ⟨hRW,hRlog,hEuler⟩ := hN (nthPrime k) hk
  exact referenceLower_zero_tail_finite k W (by omega) hW1 hW2 hRW hRlog hEuler s hs

#print axioms referenceLower_zero_tail_finite
#print axioms exists_referenceLower_zero_tail
end Erdos970.RecursiveSieve.Buchstab
