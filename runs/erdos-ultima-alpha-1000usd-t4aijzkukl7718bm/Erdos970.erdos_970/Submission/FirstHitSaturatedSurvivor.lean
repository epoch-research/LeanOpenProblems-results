import Submission.FirstHitSaturatedMain
import Submission.FirstHitPrimeSurvivor

/-! Transfer of the cubic-saturated first-hit main term to actual interval survivors. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma saturated_reference_prior_main_le (k : ℕ) (L : ℝ)
    (hbound : ∀ i : Fin k, firstPrimeList k i ≤ saturatedHitPrimeCut L 0) :
    (∑ i : Fin k, (1 / (firstPrimeList k i : ℝ)) /
      normalizer (fun j => 1 / (firstPrimeList k j : ℝ))
        (priorDivisorSupport (firstPrimeList k) i (firstHitCutoff L (firstPrimeList k i)))) ≤ saturatedHitMainSum L := by
  simp_rw [reference_prior_normalizer]
  have hsub : univ.image (firstPrimeList k) ⊆ (saturatedHitPrimeCut L 0 + 1).primesBelow := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨firstPrimeList_prime k i, hbound i⟩
  rw [← sum_image (f := fun p : ℕ => (1 / (p : ℝ)) /
    primeNormalizer p.primesBelow (firstHitCutoff L p)) (s := univ)
    (firstPrimeList_strictMono k).injective.injOn]
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro p hp hn
  have hpp := (WeightedMertens.mem_primes.mp hp).1
  have hG := primeNormalizer_ge_one p.primesBelow (firstHitCutoff L p)
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) (firstHitCutoff_pos L p)
  positivity

lemma saturatedHit_top_log_bound (L : ℝ) (hL : 0 ≤ L) :
    0 < saturatedHitPrimeCut L 0 ∧ log (saturatedHitPrimeCut L 0 : ℝ) ≤ 25 * L / 54 := by
  have he : 1 ≤ exp (L / (2 * saturatedHitNode 0 + 1)) := by
    apply one_le_exp
    norm_num [saturatedHitNode, firstHitNode]
    positivity
  have hZ : 0 < saturatedHitPrimeCut L 0 := by
    change 1 ≤ ⌊exp (L / (2 * saturatedHitNode 0 + 1))⌋₊
    apply Nat.le_floor
    simpa only [Nat.cast_one] using he
  refine ⟨hZ, ?_⟩
  have hh := log_le_log (show (0 : ℝ) < saturatedHitPrimeCut L 0 by exact_mod_cast hZ)
    (Nat.floor_le (exp_pos (L / (2 * saturatedHitNode 0 + 1))).le)
  rw [log_exp] at hh
  norm_num [saturatedHitNode, firstHitNode] at hh
  linarith

lemma saturatedHit_total_cutoff_cost (L : ℝ) (hL : 0 ≤ L) :
    (∑ p ∈ (saturatedHitPrimeCut L 0 + 1).primesBelow, (firstHitCutoff L p : ℝ) ^ 2) ≤
      4 * exp L * (1 + L) := by
  have hZL := (saturatedHit_top_log_bound L hL).2
  have hs : (∑ p ∈ (saturatedHitPrimeCut L 0 + 1).primesBelow, (firstHitCutoff L p : ℝ) ^ 2) ≤
      4 * exp L * ∑ p ∈ (saturatedHitPrimeCut L 0 + 1).primesBelow, 1 / (p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hpZ⟩ := WeightedMertens.mem_primes.mp hp
    have hlp := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
      (show (p : ℝ) ≤ saturatedHitPrimeCut L 0 by exact_mod_cast hpZ)
    convert firstHitCutoff_sq_le L p hpp.pos (by linarith) using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (initial_prime_reciprocal_le_harmonic (saturatedHitPrimeCut L 0))
    (show 0 ≤ 4 * exp L by positivity)
  have hh' := mul_le_mul_of_nonneg_left (show 1 + log (saturatedHitPrimeCut L 0 : ℝ) ≤ 1 + L by linarith)
    (show 0 ≤ 4 * exp L by positivity)
  exact hs.trans (hh.trans hh')

lemma saturated_reference_prior_cost_le (k : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ i : Fin k, firstPrimeList k i ≤ saturatedHitPrimeCut L 0) :
    (∑ i : Fin k, ((priorDivisorSupport (firstPrimeList k) i
      (firstHitCutoff L (firstPrimeList k i))).card : ℝ) ^ 2) ≤ 4 * exp L * (1 + L) := by
  have h0 : (∑ i : Fin k, ((priorDivisorSupport (firstPrimeList k) i
      (firstHitCutoff L (firstPrimeList k i))).card : ℝ) ^ 2) ≤
      ∑ i : Fin k, (firstHitCutoff L (firstPrimeList k i) : ℝ) ^ 2 := by
    apply sum_le_sum
    intro i hi
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast priorDivisorSupport_card_le _ (firstPrimeList_prime k)
      (firstPrimeList_strictMono k).injective i (firstHitCutoff L (firstPrimeList k i))
  have hsub : univ.image (firstPrimeList k) ⊆ (saturatedHitPrimeCut L 0 + 1).primesBelow := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨firstPrimeList_prime k i, hbound i⟩
  have h1 : (∑ i : Fin k, (firstHitCutoff L (firstPrimeList k i) : ℝ) ^ 2) ≤
      ∑ p ∈ (saturatedHitPrimeCut L 0 + 1).primesBelow, (firstHitCutoff L p : ℝ) ^ 2 := by
    rw [← sum_image (f := fun p : ℕ => (firstHitCutoff L p : ℝ) ^ 2) (s := univ)
      (firstPrimeList_strictMono k).injective.injOn]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => sq_nonneg _)
  exact h0.trans (h1.trans (saturatedHit_total_cutoff_cost L hL))

/-- A first-hit certificate with a fixed absolute remainder bound, transferred
from the initial prime list to an arbitrary prime set. -/
theorem prime_survivor_of_saturatedHitMainSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hbound : ∀ i : Fin P.card, firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0)
    (hmain : saturatedHitMainSum L ≤ 1 - 1 / (200 * L))
    (hm : 200 * L * (1 + 4 * exp L * (1 + L)) < (m : ℝ)) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  let q : Fin P.card → ℝ := fun i => 1 / (p i : ℝ)
  let q' : Fin P.card → ℝ := fun i => 1 / (firstPrimeList P.card i : ℝ)
  let D (i : Fin P.card) := priorDivisorSupport (firstPrimeList P.card) i
    (firstHitCutoff L (firstPrimeList P.card i))
  have hq' (i : Fin P.card) : 0 < q' i ∧ q' i < 1 := by
    have hh : (1 : ℝ) < firstPrimeList P.card i := by exact_mod_cast (firstPrimeList_prime P.card i).one_lt
    dsimp [q']
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hh⟩
  have hq (i : Fin P.card) : q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1 := by
    have ha : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hb : (0 : ℝ) < firstPrimeList P.card i := by exact_mod_cast (firstPrimeList_prime P.card i).pos
    have hab : (firstPrimeList P.card i : ℝ) ≤ p i := by exact_mod_cast nth_prime_le_sorted p hp hmono i
    exact ⟨(div_lt_one (by linarith)).mpr ha, one_div_le_one_div_of_le hb hab, (hq' i).2.le⟩
  have hDn (i : Fin P.card) : (D i).Nonempty :=
    priorDivisorSupport_nonempty _ _ _ (firstHitCutoff_pos L _)
  have hD (i : Fin P.card) : ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i :=
    priorDivisorSupport_downward _ (fun j => (firstPrimeList_prime P.card j).one_lt.le) _ _
  have hprior (i : Fin P.card) : ∀ T ∈ D i, ∀ j ∈ T, j < i := priorDivisorSupport_prior _ _ _
  have hmean := (saturated_reference_prior_main_le P.card L hbound).trans hmain
  have hcost := saturated_reference_prior_cost_le P.card L hL.le hbound
  have hobjective : (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) +
      1 + (∑ i, ((D i).card : ℝ) ^ 2) < m := by
    have hh := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg m)
    have hmc : 1 + 4 * exp L * (1 + L) < (m : ℝ) / (200 * L) := by
      apply (lt_div_iff₀ (by positivity : 0 < 200 * L)).mpr
      nlinarith only [hm]
    change (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) ≤ _ at hh
    change (∑ i, ((D i).card : ℝ) ^ 2) ≤ _ at hcost
    linear_combination hh + hcost + hmc
  obtain ⟨j, hj, hjall⟩ := survivor_of_dominating_first_hit q q' hq hq' D hDn hD hprior m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) hobjective
  refine ⟨j, hj, ?_⟩
  intro a ha
  have hrange : a ∈ Set.range p := by simpa only [p, Finset.range_orderEmbOfFin, mem_coe] using ha
  obtain ⟨i, rfl⟩ := hrange
  exact of_decide_eq_false (hjall i)

/-- A uniform Jacobsthal bound once the real scale contains the first k primes. -/
theorem isJacobsthalBound_of_saturatedHitMainSum (k : ℕ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hbound : Nat.nth Nat.Prime k ≤ saturatedHitPrimeCut L 0)
    (hmain : saturatedHitMainSum L ≤ 1 - 1 / (200 * L))
    (hm : 200 * L * (1 + 4 * exp L * (1 + L)) < (m : ℝ)) : IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  have hb (i : Fin P.card) : firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0 :=
    (Nat.nth_monotone Nat.infinite_setOf_prime (show i.val ≤ k by omega)).trans hbound
  obtain ⟨j, hj, havoid⟩ := prime_survivor_of_saturatedHitMainSum P hP r L hL m hb hmain hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

#print axioms isJacobsthalBound_of_saturatedHitMainSum
end Erdos970.FiniteSelberg
