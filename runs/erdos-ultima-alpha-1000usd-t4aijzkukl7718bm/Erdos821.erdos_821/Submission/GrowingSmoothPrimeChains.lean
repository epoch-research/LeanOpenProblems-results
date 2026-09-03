import Submission.GrowingLargeChildDepth
import Submission.SparseSmoothPrimeChains
import Submission.LargeChildAvoidingTrees

/-!
# Growing prime-chain depths forced by the hypothetical negation

All conclusions in this file retain an explicit hypothesis that Erdos 821 is
false. They do not prove that hypothesis or obtain a contradiction from it.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

lemma exists_reciprocal_exponent_above (b : ℝ) (hb : b < 1) :
    ∃ R : ℕ, 1 ≤ R ∧ b ≤ 1-1/(R : ℝ) := by
  obtain ⟨R, hR⟩ := exists_nat_gt (1+1/(1-b))
  have hbpos : 0 < 1-b := by linarith
  have hinv : 0 < 1/(1-b) := one_div_pos.mpr hbpos
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hi : 1/(1-b) ≤ (R : ℝ) := by linarith
  have hm : 1 ≤ (R : ℝ)*(1-b) := (div_le_iff₀ hbpos).mp hi
  have hdiv : 1/(R : ℝ) ≤ 1-b :=
    (div_le_iff₀ hRpos).mpr (by nlinarith only [hm])
  exact ⟨R, by exact_mod_cast hR1, by linarith⟩

lemma exists_sparse_reciprocal_rootSmoothPrimeSet_of_negation
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k R : ℕ, 3 ≤ k ∧ 1 ≤ R ∧
      Summable ((rootSmoothPrimeSet k).indicator
        (fun p : ℕ => (p : ℝ)^(-(1-1/(R : ℝ))))) := by
  obtain ⟨k, hk, b, _, hb, Hsum⟩ := exists_sparse_rootSmoothPrimeSet_of_negation Hneg
  obtain ⟨R, hR, hbR⟩ := exists_reciprocal_exponent_above b hb
  exact ⟨k, R, hk, hR,
    summable_set_power_mono (rootSmoothPrimeSet k) b (1-1/(R : ℝ)) hbR Hsum⟩

lemma zero_not_mem_rootSmoothPrimeSet (k : ℕ) : 0 ∉ rootSmoothPrimeSet k := by
  intro h
  exact Nat.not_prime_zero h.1

/-- Conditional on the exact negation, the ancestor depth grows with the
cutoff while retaining every fixed power of its binary-logarithm saving. -/
theorem negation_forces_growing_sparse_layers
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k R : ℕ, 3 ≤ k ∧ 1 ≤ R ∧ ∀ J : ℕ, ∀ᶠ L : ℕ in atTop,
      (largeChildDepthScale k R L)^J *
        largeChildLayerCount k (rootSmoothPrimeSet k) L (largeChildDepthCutoff k R L) ≤
          largeChildDepthCutoff k R L := by
  obtain ⟨k, R, hk, hR, Hsum⟩ :=
    exists_sparse_reciprocal_rootSmoothPrimeSet_of_negation Hneg
  exact ⟨k, R, hk, hR, fun J => eventually_growing_largeChildLayer_count_small
    k R (by omega) hR (rootSmoothPrimeSet k) (zero_not_mem_rootSmoothPrimeSet k) Hsum J⟩

/-- Conditional on the exact negation, at least half the primes below the
cutoff start avoiding paths of length L, eventually as L tends to infinity. -/
theorem negation_forces_growing_many_avoiding_paths
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k R : ℕ, 3 ≤ k ∧ 1 ≤ R ∧ ∀ᶠ L : ℕ in atTop,
      (largeChildDepthCutoff k R L + 1).primesBelow.card ≤
        2 * (((largeChildDepthCutoff k R L + 1).primesBelow).filter
          (fun p => largeChildAvoidingPath k (rootSmoothPrimeSet k) L p)).card := by
  obtain ⟨k, R, hk, hR, Hsum⟩ :=
    exists_sparse_reciprocal_rootSmoothPrimeSet_of_negation Hneg
  refine ⟨k, R, hk, hR, ?_⟩
  filter_upwards [eventually_growing_prime_complement_large k R (by omega) hR
    (rootSmoothPrimeSet k) (zero_not_mem_rootSmoothPrimeSet k) Hsum] with L hL
  refine hL.trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
  intro p hp
  obtain ⟨hpP, hpL⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpP, outside_largeChildLayer_has_avoiding_path
    k (rootSmoothPrimeSet k) (prime_outside_rootSmoothPrimeSet_has_large_child k)
    L p (Nat.mem_primesBelow.mp hpP).2 hpL⟩

/-- The full consequence avoids the smooth set along every eligible branch,
not just one selected path. The negation remains an explicit hypothesis. -/
theorem negation_forces_growing_many_avoiding_trees
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k R : ℕ, 3 ≤ k ∧ 1 ≤ R ∧ ∀ᶠ L : ℕ in atTop,
      (largeChildDepthCutoff k R L + 1).primesBelow.card ≤
        2 * (((largeChildDepthCutoff k R L + 1).primesBelow).filter
          (fun p => largeChildAvoidingTree k (rootSmoothPrimeSet k) L p)).card := by
  obtain ⟨k, R, hk, hR, Hsum⟩ :=
    exists_sparse_reciprocal_rootSmoothPrimeSet_of_negation Hneg
  refine ⟨k, R, hk, hR, ?_⟩
  filter_upwards [eventually_growing_prime_complement_large k R (by omega) hR
    (rootSmoothPrimeSet k) (zero_not_mem_rootSmoothPrimeSet k) Hsum] with L hL
  refine hL.trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
  intro p hp
  obtain ⟨hpP, hpL⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpP, (largeChildAvoidingTree_iff k (rootSmoothPrimeSet k) L p).mpr
    ⟨(Nat.mem_primesBelow.mp hpP).2, hpL⟩⟩

end Erdos821
