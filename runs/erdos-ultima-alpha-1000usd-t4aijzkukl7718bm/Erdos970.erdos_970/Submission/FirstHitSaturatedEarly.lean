import Submission.FirstHitCubeBridge

/-! Exact split of the early-prime range into a cubic-normalizer bridge,
a seventh-moment far tail, and an exact finite wheel. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma sum_initial_primes_split (a b : ℕ) (hab : a ≤ b) (f : ℕ → ℝ) :
    (∑ p ∈ (b + 1).primesBelow, f p) =
      (∑ p ∈ (Ioc a b).filter Nat.Prime, f p) + ∑ p ∈ (a + 1).primesBelow, f p := by
  have hsub : (a + 1).primesBelow ⊆ (b + 1).primesBelow := by
    intro p hp
    obtain ⟨hpp, hpa⟩ := WeightedMertens.mem_primes.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨hpp, hpa.trans hab⟩
  have he : ((b + 1).primesBelow \ (a + 1).primesBelow : Finset ℕ) =
      (Ioc a b).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, mem_filter, mem_Ioc, WeightedMertens.mem_primes]
    constructor
    · rintro ⟨⟨hpp, hpb⟩, hn⟩
      refine ⟨⟨?_, hpb⟩, hpp⟩
      by_contra h
      exact hn ⟨hpp, by omega⟩
    · rintro ⟨⟨hlo, hhi⟩, hpp⟩
      exact ⟨⟨hpp, hhi⟩, fun hh => (not_le_of_gt hlo) hh.2⟩
  have hh := sum_sdiff (f := f) hsub
  rw [he] at hh
  exact hh.symm

lemma firstHitFarCut_log_bound (L : ℝ) (hL : 0 ≤ L) :
    0 < firstHitFarCut L ∧ 9 * log (firstHitFarCut L : ℝ) ≤ L := by
  have he : 1 ≤ exp (L / 9) := one_le_exp (by positivity)
  have hF : 0 < firstHitFarCut L := by
    change 1 ≤ ⌊exp (L / 9)⌋₊
    apply Nat.le_floor
    simpa only [Nat.cast_one] using he
  have hh := log_le_log (show (0 : ℝ) < firstHitFarCut L by exact_mod_cast hF)
    (Nat.floor_le (exp_pos (L / 9)).le)
  rw [log_exp] at hh
  exact ⟨hF, by linarith⟩

lemma firstHitFarCut_le_cubeCut (L : ℝ) (hL : 0 ≤ L) :
    firstHitFarCut L ≤ firstHitPrimeCut L 23 := by
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  norm_num [firstHitNode]
  linarith

noncomputable def saturatedEarlyMain : ℝ := 1 / 15 + 54 / 1519
noncomputable def saturatedEarlyError : ℝ :=
  firstHitBridgeError + 972 * WeightedMertens.sharpMomentError / 217

lemma saturatedEarlyError_nonneg : 0 ≤ saturatedEarlyError := by
  unfold saturatedEarlyError
  have := firstHitBridgeError_nonneg
  have := WeightedMertens.sharpMomentError_pos
  positivity

theorem firstHit_saturated_early_sum_bound (L : ℝ) (hL : 0 < L)
    (hsmall : 9 * log 2 ≤ L) (W : ℕ) (hW : 0 < W) (hWF : W ≤ firstHitFarCut L)
    (hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L)
    (hthreshold : ∀ p, p.Prime → W < p → FirstHitLogThresholds p)
    (hEuler : ∀ p : ℕ, W ≤ p → eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    (∑ p ∈ (firstHitPrimeCut L 23 + 1).primesBelow, firstHitMeanExcess L p) ≤
      saturatedEarlyMain / L + saturatedEarlyError / L ^ 2 := by
  let F := firstHitFarCut L
  let P := (F + 1).primesBelow.filter (fun p => W < p)
  have hF := (firstHitFarCut_log_bound L hL.le).1
  have hFL := (firstHitFarCut_log_bound L hL.le).2
  have hfar := first_hit_far_sum_bound F hF L hL hFL P (filter_subset _ _)
    (firstHitCutoff L) (fun p _ => firstHitCutoff_pos L p)
    (fun p _ => firstHitCutoff_log_lower L p)
    (fun p hp => (hthreshold p (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (mem_filter.mp hp).2).1)
    (fun p hp => (hthreshold p (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (mem_filter.mp hp).2).2.1)
  have hpart := sum_filter_add_sum_filter_not (F + 1).primesBelow (fun p => W < p) (firstHitMeanExcess L)
  have hz : (∑ p ∈ (F + 1).primesBelow with ¬W < p, firstHitMeanExcess L p) = 0 := by
    apply sum_eq_zero
    intro p hp
    exact firstHitMeanExcess_zero_on_wheel W hW L hWheel p
      (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (by have := (mem_filter.mp hp).2; omega)
  rw [hz, add_zero] at hpart
  change (∑ p ∈ P, firstHitMeanExcess L p) = _ at hpart
  change (∑ p ∈ P, firstHitMeanExcess L p) ≤ _ at hfar
  rw [hpart] at hfar
  have hbridgeMem (p : ℕ) (hp : p ∈ firstHitBridgePrimes L) : p.Prime ∧ W < p := by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    exact ⟨hpp, hWF.trans_lt (mem_Ioc.mp hpI).1⟩
  have hbridge := firstHit_bridge_sum_le L hL hsmall
    (fun p hp => (hthreshold p (hbridgeMem p hp).1 (hbridgeMem p hp).2).2.2)
    (fun p hp => hEuler p (hbridgeMem p hp).2.le)
  rw [sum_initial_primes_split (firstHitFarCut L) _ (firstHitFarCut_le_cubeCut L hL.le)]
  change (∑ p ∈ firstHitBridgePrimes L, firstHitMeanExcess L p) +
    (∑ p ∈ (F + 1).primesBelow, firstHitMeanExcess L p) ≤ _
  unfold saturatedEarlyMain saturatedEarlyError
  linear_combination hbridge + hfar

#print axioms firstHit_saturated_early_sum_bound
end Erdos970.FiniteSelberg
