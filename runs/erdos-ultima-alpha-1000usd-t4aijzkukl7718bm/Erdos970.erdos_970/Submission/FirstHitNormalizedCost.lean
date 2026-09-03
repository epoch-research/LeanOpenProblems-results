import Submission.FirstHitSharpTransfer
import Submission.FirstHitSaturatedSurvivor
import Submission.PrimeInverseLogMoments

/-! Normalizer-sensitive coefficient costs for the reference first-hit sieve.
All estimates here are unconditional; the main-term slack is used separately. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma primeNormalizer_strict_log_lower (p R : ℕ) (hp : p.Prime) (hR : 0 < R)
    (hlog : log (p : ℝ) / 2 ≤ log (R : ℝ)) :
    log (p : ℝ) / 4 ≤ primeNormalizer p.primesBelow R := by
  let N := min R p
  have hN : 0 < N := lt_min hR hp.pos
  have hNp : N ≤ p := min_le_right _ _
  have hNR : N ≤ R := min_le_left _ _
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hlN : log (p : ℝ) / 2 ≤ log (N : ℝ) := by
    dsimp only [N]
    rcases le_total R p with h | h
    · rw [Nat.min_eq_left h]
      exact hlog
    · rw [Nat.min_eq_right h]
      linarith
  have hh : log (N : ℝ) ≤ primeNormalizer (p+1).primesBelow N := by
    apply (log_le_harmonic_floor (N : ℝ) hN0.le).trans
    rw [Nat.floor_natCast]
    exact harmonic_le_smallDivisorFamily _
      (fun q hq => (WeightedMertens.mem_primes.mp hq).1) N
      (fun q hq hqN => WeightedMertens.mem_primes.mpr ⟨hq,hqN.trans hNp⟩)
  have hd : (1/2 : ℝ) ≤ 1-1/(p : ℝ) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    linarith
  have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ 1-1/(p : ℝ))
  have hs := normalizer_strict_prefix_ge (N := N) hp
  have hmono := primeNormalizer_cutoff_mono p.primesBelow
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) hNR
  have hhalf := mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ log (N : ℝ))
  nlinarith

lemma prime_canonical_cost_le_of_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (R : ℕ) (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : D ⊆ divisorSupport p R) :
    kernelCost (fun i => 1/(p i : ℝ))
      (canonicalOrthogonal (fun i => 1/(p i : ℝ)) D) ≤
      exp 2 * R / normalizer (fun i => 1/(p i : ℝ)) D := by
  have hq := prime_marginals p hp
  rw [kernelCost_canonical _ hq D hDn]
  apply div_le_div_of_nonneg_right _ (normalizer_pos _ hq D hDn).le
  have hf (i : ι) : (1+1/(p i : ℝ))/(1-1/(p i : ℝ)) =
      ((p i : ℝ)+1)/(p i-1) := by
    have h0 : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    field_simp
  simp_rw [hf]
  apply (sum_le_sum_of_subset_of_nonneg hD ?_).trans (divisor_cost_sum_le p hp hpinj R)
  intro Q _ _
  apply prod_nonneg
  intro i _
  have h1 : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
  exact div_nonneg (by positivity) (by linarith)

noncomputable def inverseLogSquareConstant : ℝ := 4+16*(WeightedMertens.boundConstant+1)

lemma inverseLogSquareConstant_pos : 0 < inverseLogSquareConstant := by
  unfold inverseLogSquareConstant
  have := WeightedMertens.boundConstant_pos
  positivity

/-- An absolute convergent prime sum, including the endpoint prime two. -/
lemma prime_inv_log_square_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, 1/((p : ℝ)*log p^2)) ≤ inverseLogSquareConstant := by
  let Z := max 2 (P.sup id)
  let S := (Ioc 2 Z).filter Nat.Prime
  have hZ : 2 ≤ Z := le_max_left _ _
  have hZR : (2 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hsub : P ⊆ insert 2 S := by
    intro p hp
    by_cases h2 : p = 2
    · exact h2 ▸ mem_insert_self _ _
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (hP p hp).two_le; omega,
        (le_sup (f := id) hp).trans (le_max_right _ _)⟩,hP p hp⟩
  have hsum := sum_le_sum_of_subset_of_nonneg
    (f := fun p : ℕ => 1/((p : ℝ)*log p^2)) hsub (fun p _ _ => by positivity)
  have h2 : 2 ∉ S := by simp [S]
  rw [sum_insert h2] at hsum
  have he := (abs_le.mp (WeightedMertens.abs_inverseLogPrimeInterval_sub 1
    (a := 2) (b := Z) (by norm_num) hZR)).2
  have hid : WeightedMertens.inverseLogPrimeInterval 1 2 (Z : ℝ) =
      ∑ p ∈ S, 1/((p : ℝ)*log p^2) := by
    simp [WeightedMertens.inverseLogPrimeInterval,S]
  rw [hid] at he
  norm_num only [Nat.reduceAdd, Nat.cast_one, Nat.cast_ofNat] at he
  have hl2 : (1/2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hlZ : 0 ≤ log (Z : ℝ) := log_nonneg (by linarith)
  have hB := WeightedMertens.boundConstant_pos
  have hsq : (1 : ℝ)/log 2^2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < log 2))).mpr
    nlinarith
  have hcube : (1 : ℝ)/log 2^3 ≤ 8 := by
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < log 2) 3)).mpr
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hl2 3
    norm_num at hh
    linarith
  have hm := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 2*(WeightedMertens.boundConstant+1) by positivity)
  simp only [mul_one_div] at hm
  have hz : 0 ≤ (1 : ℝ)/log (Z : ℝ)^2 := by positivity
  unfold inverseLogSquareConstant
  have hident : 1 / ((2 : ℝ)*log 2^2) = (1/log 2^2)/2 := by ring
  norm_num only [Nat.cast_ofNat] at hsum
  rw [hident] at hsum
  nlinarith

noncomputable def normalizedFirstHitCostConstant : ℝ :=
  64 * exp 4 * inverseLogSquareConstant

lemma normalizedFirstHitCostConstant_pos : 0 < normalizedFirstHitCostConstant := by
  unfold normalizedFirstHitCostConstant
  exact mul_pos (by positivity) inverseLogSquareConstant_pos

/-- The squared costs sum to O(exp L), uniformly in the prime budget.
The reciprocal-log normalizer is retained, unlike the cardinality estimate. -/
theorem saturated_reference_normalized_cost (k : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ i : Fin k, firstPrimeList k i ≤ saturatedHitPrimeCut L 0) :
    (∑ i : Fin k, kernelCost (fun j => 1/(firstPrimeList k j : ℝ))
      (canonicalOrthogonal (fun j => 1/(firstPrimeList k j : ℝ))
        (priorDivisorSupport (firstPrimeList k) i (firstHitCutoff L (firstPrimeList k i))))^2) ≤
      normalizedFirstHitCostConstant * exp L := by
  let p := firstPrimeList k
  let q := fun i => 1/(p i : ℝ)
  let R := fun i => firstHitCutoff L (p i)
  let D := fun i => priorDivisorSupport p i (R i)
  have hp := firstPrimeList_prime k
  have hpinj := (firstPrimeList_strictMono k).injective
  have hterm (i : Fin k) :
      kernelCost q (canonicalOrthogonal q (D i))^2 ≤
        (64*exp 4*exp L) * (1/((p i : ℝ)*log (p i)^2)) := by
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hlp : 0 < log (p i : ℝ) := log_pos (by exact_mod_cast (hp i).one_lt)
    have hlog := (log_le_log hp0 (show (p i : ℝ) ≤ saturatedHitPrimeCut L 0 by
      exact_mod_cast hbound i)).trans (saturatedHit_top_log_bound L hL).2
    have hG := primeNormalizer_strict_log_lower (p i) (R i) (hp i)
      (firstHitCutoff_pos L _) ((by linarith : log (p i : ℝ)/2 ≤ (L-log (p i))/2).trans
        (firstHitCutoff_log_lower L _))
    rw [← reference_prior_normalizer k i (R i)] at hG
    have hc := prime_canonical_cost_le_of_subset p hp hpinj (R i) (D i)
      (priorDivisorSupport_nonempty p i (R i) (firstHitCutoff_pos L _)) (filter_subset _ _)
    have hG0 : 0 < normalizer q (D i) := (by linarith : 0 < log (p i : ℝ)/4).trans_le hG
    have hu : kernelCost q (canonicalOrthogonal q (D i)) ≤
        4*exp 2*(R i : ℝ)/log (p i) := by
      calc
        _ ≤ exp 2*(R i : ℝ)/normalizer q (D i) := hc
        _ ≤ exp 2*(R i : ℝ)/(log (p i)/4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hG
        _ = _ := by ring
    have hc0 : 0 ≤ kernelCost q (canonicalOrthogonal q (D i)) :=
      sum_nonneg (fun _ _ => abs_nonneg _)
    have hs := pow_le_pow_left₀ hc0 hu 2
    have hR := firstHitCutoff_sq_le L (p i) (hp i).pos (by linarith)
    have hR' := mul_le_mul_of_nonneg_left hR (show 0 ≤ 16*exp 4 / log (p i)^2 by positivity)
    have he : (exp (2 : ℝ))^2 = exp 4 := by rw [← exp_nat_mul]; norm_num
    rw [div_pow, mul_pow, mul_pow, he] at hs
    norm_num only [show (4 : ℝ)^2 = 16 by norm_num] at hs
    change (R i : ℝ)^2 ≤ _ at hR
    convert hs.trans (by convert hR' using 1 <;> ring) using 1 <;> ring
  have hsum := sum_le_sum (s := univ) (fun i _ => hterm i)
  rw [← mul_sum] at hsum
  have hS := prime_inv_log_square_sum_le (univ.image p) (by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact hp i)
  rw [sum_image hpinj.injOn] at hS
  have hh := mul_le_mul_of_nonneg_left hS (show 0 ≤ 64*exp 4*exp L by positivity)
  exact hsum.trans (by simpa only [normalizedFirstHitCostConstant, mul_assoc, mul_comm, mul_left_comm] using hh)

#print axioms saturated_reference_normalized_cost
end Erdos970.FiniteSelberg
