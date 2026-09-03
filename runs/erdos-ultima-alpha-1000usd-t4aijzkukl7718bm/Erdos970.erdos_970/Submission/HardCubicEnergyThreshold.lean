import Submission.HardCubicPrimeEnergy

/-! Absorption of the accumulated hard-jump error using a fixed small-prime
split. All cutoffs here are absolute constants, not growing accuracy parameters. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 1000000

lemma initial_prime_reciprocal_linear (R B : ℕ) (hR : 0 < R) (hB : 2 ≤ B) :
    (∑ p ∈ (R + 1).primesBelow, 1 / (p : ℝ)) ≤
      (B : ℝ) + (log R + WeightedMertens.boundConstant) / log B := by
  let P := (R + 1).primesBelow
  have hlogB : 0 < log (B : ℝ) := log_pos (by exact_mod_cast (show 1 < B by omega))
  have hsplit := sum_filter_add_sum_filter_not P (fun p => p ≤ B) (fun p => 1 / (p : ℝ))
  have hsmall : (∑ p ∈ P.filter (fun p => p ≤ B), 1 / (p : ℝ)) ≤ B := by
    have hsub : P.filter (fun p => p ≤ B) ⊆ Icc 1 B := by
      intro p hp
      obtain ⟨hpP, hpB⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(WeightedMertens.mem_primes.mp hpP).1.pos, hpB⟩
    calc
      _ ≤ ∑ _p ∈ P.filter (fun p => p ≤ B), (1 : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp (hsub hp)).1
        exact (div_le_one (by linarith : (0 : ℝ) < p)).mpr hp1
      _ = ((P.filter (fun p => p ≤ B)).card : ℝ) := by simp
      _ ≤ B := by exact_mod_cast ((card_le_card hsub).trans_eq (by simp))
  have hlarge : (∑ p ∈ P.filter (fun p => ¬p ≤ B), 1 / (p : ℝ)) ≤
      WeightedMertens.primeSum R / log B := by
    calc
      _ ≤ (∑ p ∈ P.filter (fun p => ¬p ≤ B), log (p : ℝ) / p) / log B := by
        rw [sum_div]
        apply sum_le_sum
        intro p hp
        have hpp := (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hl : log (B : ℝ) ≤ log p :=
          log_le_log (by exact_mod_cast (show 0 < B by omega))
            (by exact_mod_cast (show B ≤ p by have := (mem_filter.mp hp).2; omega))
        apply (le_div_iff₀ hlogB).mpr
        apply (le_div_iff₀ hp0).mpr
        have he : ((1 / (p : ℝ)) * log B) * p = log B := by field_simp
        rwa [he]
      _ ≤ WeightedMertens.primeSum R / log B := by
        apply div_le_div_of_nonneg_right _ hlogB.le
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p _ _ => div_nonneg (log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hu := (abs_le.mp (WeightedMertens.abs_primeSum_sub_log R hR)).2
  have hu' := div_le_div_of_nonneg_right
    (show WeightedMertens.primeSum R ≤ log R + WeightedMertens.boundConstant by linarith) hlogB.le
  linarith

noncomputable def hardCubicJumpScale : ℝ := 3200000000 * additiveNormalizerConstant
noncomputable def hardCubicSmallSplit : ℕ := ⌈exp (hardCubicJumpScale + 1)⌉₊ + 2
noncomputable def hardCubicEnergyThreshold : ℝ :=
  1 + 800000000 * additiveNormalizerConstant + 1000000000 * WeightedMertens.sharpMomentError +
    hardCubicJumpScale * (hardCubicSmallSplit + 1) + WeightedMertens.boundConstant

lemma hardCubicJumpScale_pos : 0 < hardCubicJumpScale := by
  unfold hardCubicJumpScale
  exact mul_pos (by norm_num) additiveNormalizerConstant_pos

lemma hardCubicSmallSplit_ge : 2 ≤ hardCubicSmallSplit := by unfold hardCubicSmallSplit; omega

lemma hardCubicSmallSplit_log : hardCubicJumpScale + 1 ≤ log (hardCubicSmallSplit : ℝ) := by
  have hh := Nat.le_ceil (exp (hardCubicJumpScale + 1))
  have hbig : exp (hardCubicJumpScale + 1) ≤ (hardCubicSmallSplit : ℝ) := by
    unfold hardCubicSmallSplit
    push_cast
    linarith
  simpa only [log_exp] using log_le_log (exp_pos _) hbig

lemma hardCubicEnergyThreshold_pos : 0 < hardCubicEnergyThreshold := by
  unfold hardCubicEnergyThreshold
  have := additiveNormalizerConstant_pos
  have := WeightedMertens.sharpMomentError_pos
  have := WeightedMertens.boundConstant_pos
  have := hardCubicJumpScale_pos
  positivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma prime_hardCubic_error_absorbed (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 2877 / 10000) :
    800000000 * additiveNormalizerConstant + 1000000000 * WeightedMertens.sharpMomentError +
      3200000000 * additiveNormalizerConstant * ∑ i, 1 / (p i : ℝ) ≤
      log R + hardCubicEnergyThreshold := by
  let B := hardCubicSmallSplit
  let A := hardCubicJumpScale
  let L := log (R : ℝ)
  have hB : 2 ≤ B := hardCubicSmallSplit_ge
  have hA : 0 < A := hardCubicJumpScale_pos
  have hAB : A + 1 ≤ log (B : ℝ) := hardCubicSmallSplit_log
  have hlogB : 0 < log (B : ℝ) := by linarith
  have hs := cappedLogMoment_split p hp hinj R hR hfull 0
  simp only [cappedLogMoment, pow_zero, one_mul] at hs
  have hi := initial_prime_reciprocal_linear R B hR hB
  have hrec : (∑ i, 1 / (p i : ℝ)) ≤ (B : ℝ) + (L + WeightedMertens.boundConstant) / log B + 1 := by
    rw [hs]
    dsimp only [L]
    linarith
  have hr := mul_le_mul_of_nonneg_left hrec hA.le
  have hbase : 0 ≤ L + WeightedMertens.boundConstant :=
    add_nonneg (log_natCast_nonneg R) WeightedMertens.boundConstant_pos.le
  have hdiv : A * ((L + WeightedMertens.boundConstant) / log B) ≤ L + WeightedMertens.boundConstant := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogB).mpr
    exact mul_le_mul_of_nonneg_right (by linarith : A ≤ log (B : ℝ)) hbase |>.trans_eq (mul_comm _ _)
  unfold hardCubicEnergyThreshold
  change _ ≤ L + (1 + 800000000 * additiveNormalizerConstant + 1000000000 * WeightedMertens.sharpMomentError +
    A * (B + 1) + WeightedMertens.boundConstant)
  change 800000000 * additiveNormalizerConstant + 1000000000 * WeightedMertens.sharpMomentError + A * _ ≤ _
  linarith

/-- Once one absolute threshold is reached, the hard-cubic kernel has
  positive seventh-degree logarithmic energy at the certified tail budget. -/
theorem prime_hardCubic_energy (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hlarge : hardCubicEnergyThreshold ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 2877 / 10000) :
    log (R : ℝ) ^ 7 ≤ kernelEnergy (fun i => 1 / (p i : ℝ))
      (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) := by
  have he := prime_hardCubic_energy_lower p hp hinj R hR hfull htail
  have ha := prime_hardCubic_error_absorbed p hp hinj R hR hfull htail
  have hL : 0 ≤ log (R : ℝ) := log_natCast_nonneg R
  have hm := mul_le_mul_of_nonneg_right ha (pow_nonneg hL 6)
  have ht := mul_le_mul_of_nonneg_right hlarge (pow_nonneg hL 6)
  have hp7 := pow_nonneg hL 7
  nlinarith only [he, hm, ht, hp7]

#print axioms prime_hardCubic_error_absorbed
#print axioms prime_hardCubic_energy
end Erdos970.FiniteSelberg
