import Submission.BuchstabTailAlgebra
import Submission.BuchstabLowerTail

/-! The complete small-prime tail of the canonical upper source, normalized
at an arbitrary large prime prefix. The bound is uniform for all s>=1. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg

noncomputable def tailPrimeCut (L : ℝ) : ℕ := ⌊exp (L/13)⌋₊
noncomputable def smallPrimePart (k : ℕ) (L : ℝ) : Finset ℕ :=
  (nthPrime k).primesBelow.filter (fun p => p ≤ tailPrimeCut L)

lemma tailPrimeCut_pos (L : ℝ) (hL : 0 ≤ L) : 0 < tailPrimeCut L :=
  Nat.floor_pos.mpr (one_le_exp (by linarith))

lemma tailPrimeCut_log_le (L : ℝ) (hL : 0 ≤ L) : log (tailPrimeCut L : ℝ) ≤ L/13 := by
  have hh := log_le_log (show (0 : ℝ) < tailPrimeCut L by exact_mod_cast tailPrimeCut_pos L hL)
    (Nat.floor_le (exp_pos (L/13)).le)
  simpa only [log_exp] using hh

lemma tailPrimeCut_scaled (s L : ℝ) : tailPrimeCut (s*L) = expFloor (s/13) L := by
  unfold tailPrimeCut expFloor
  congr 2
  ring

lemma smallPrimePart_subset_cut (k : ℕ) (L : ℝ) :
    smallPrimePart k L ⊆ (tailPrimeCut L+1).primesBelow := by
  intro p hp
  obtain ⟨hpP,hpc⟩ := mem_filter.mp hp
  exact WeightedMertens.mem_primes.mpr ⟨(Nat.mem_primesBelow.mp hpP).2,hpc⟩

/-- Finite, fully explicit upper-source tail bound at the terminal grid cutoff. -/
theorem reference_initial_tail_finite (k W : ℕ) (hW : 0 < W)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (W : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (W : ℝ))
    (hRW : W*(firstHitWheel W)^2 ≤ nthPrime k)
    (hlarge : 20*truncatedTailError initialTailCoefficient ≤ initialGridTail*log (nthPrime k : ℝ))
    (hEuler : eulerMass (nthPrime k+1).primesBelow ≤ (9/5 : ℝ)*log (nthPrime k : ℝ))
    (s : ℝ) (hs : 1 ≤ s) :
    eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ smallPrimePart k (s*log (nthPrime k : ℝ)), scaledPrimeExcess (s*log (nthPrime k : ℝ)) p) ≤
        initialGridTail/s := by
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
  have hsmall : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hWR : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ nthPrime k := by exact_mod_cast hRW
    have hRexp : (nthPrime k : ℝ) ≤ exp (s*L) := by
      rw [← exp_log (show (0 : ℝ) < nthPrime k by exact_mod_cast hp.pos)]
      apply exp_le_exp.mpr
      change L ≤ s*L
      nlinarith
    exact hWR.trans hRexp
  have hsum := scaled_excess_sum_thirteenth_tail (smallPrimePart k (s*L)) R W hR hW
    (smallPrimePart_subset_cut k (s*L)) (s*L) hτ hRL hsmall hthreshold hthreshold'
  apply normalized_truncated_moment_le _ (eulerMass (nthPrime k).primesBelow) L s
    (log (R : ℝ)) initialTailCoefficient initialGridTail _
      (eulerMass_pos _ (fun p hp' => (Nat.mem_primesBelow.mp hp').2)).le
      ((eulerMass_strict_prefix_le _ hp).trans hEuler) hlog hs (log_natCast_nonneg R) hRL
      initialTailCoefficient_nonneg initialGridTail_pos.le initial_tail_main_budget hlarge
  convert hsum using 1 <;> dsimp only [initialTailCoefficient]; ring

lemma exists_tail_threshold_wheel : ∃ W : ℕ, 0 < W ∧
    50*WeightedMertens.sharpMomentError ≤ log (W : ℝ) ∧ supportMassLogThreshold ≤ log (W : ℝ) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨W,hW,h1,h2⟩ := ((eventually_ge_atTop 1).and
    ((hlog.eventually_ge_atTop (50*WeightedMertens.sharpMomentError)).and
      (hlog.eventually_ge_atTop supportMassLogThreshold))).exists
  exact ⟨W,by omega,h1,h2⟩

/-- One absolute threshold bounds the entire small-prime source tail for all
s>=1. This supplies the tail omitted by the finite sector-limit theorem. -/
theorem exists_reference_initial_tail : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ s : ℝ, 1 ≤ s → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ smallPrimePart k (s*log (nthPrime k : ℝ)), scaledPrimeExcess (s*log (nthPrime k : ℝ)) p) ≤
        initialGridTail/s := by
  obtain ⟨W,hW,h1,h2⟩ := exists_tail_threshold_wheel
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (W*(firstHitWheel W)^2)).and
    ((hlog.eventually_ge_atTop (20*truncatedTailError initialTailCoefficient/initialGridTail)).and
      eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun k hk s hs => ?_⟩
  obtain ⟨hRW,hlogR,hEuler⟩ := hN (nthPrime k) hk
  have hlarge : 20*truncatedTailError initialTailCoefficient ≤ initialGridTail*log (nthPrime k : ℝ) := by
    have hh := (div_le_iff₀ initialGridTail_pos).mp hlogR
    nlinarith only [hh]
  exact reference_initial_tail_finite k W hW h1 h2 hRW hlarge hEuler s hs

#print axioms reference_initial_tail_finite
#print axioms exists_reference_initial_tail
end Erdos970.RecursiveSieve.Buchstab
