import Submission.FirstHitNormalizedCost

/-! Unconditional survivor transfer using the normalizer-sensitive first-hit
remainder. The required main-term slack is displayed explicitly. -/
namespace Erdos970.FiniteSelberg
open Finset Real

/-- A first-hit certificate with a fixed absolute remainder bound, transferred
from the initial prime list to an arbitrary prime set. -/
theorem prime_survivor_of_saturatedHitNormalizedCost (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hbound : ∀ i : Fin P.card, firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0)
    (hmain : saturatedHitMainSum L ≤ 1 - 1 / (200 * L))
    (hm : 200 * L * (1 + normalizedFirstHitCostConstant * exp L) < (m : ℝ)) :
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
  have hcost := saturated_reference_normalized_cost P.card L hL.le hbound
  have hobjective : (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) +
      1 + (∑ i, kernelCost q' (canonicalOrthogonal q' (D i)) ^ 2) < m := by
    have hh := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg m)
    have hmc : 1 + normalizedFirstHitCostConstant * exp L < (m : ℝ) / (200 * L) := by
      apply (lt_div_iff₀ (by positivity : 0 < 200 * L)).mpr
      nlinarith only [hm]
    change (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) ≤ _ at hh
    change (∑ i, kernelCost q' (canonicalOrthogonal q' (D i)) ^ 2) ≤ _ at hcost
    linear_combination hh + hcost + hmc
  obtain ⟨j, hj, hjall⟩ := survivor_of_dominating_first_hit_cost q q' hq hq' D hDn hD hprior m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) hobjective
  refine ⟨j, hj, ?_⟩
  intro a ha
  have hrange : a ∈ Set.range p := by simpa only [p, Finset.range_orderEmbOfFin, mem_coe] using ha
  obtain ⟨i, rfl⟩ := hrange
  exact of_decide_eq_false (hjall i)

/-- A uniform Jacobsthal bound once the real scale contains the first k primes. -/
theorem isJacobsthalBound_of_saturatedHitNormalizedCost (k : ℕ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hbound : Nat.nth Nat.Prime k ≤ saturatedHitPrimeCut L 0)
    (hmain : saturatedHitMainSum L ≤ 1 - 1 / (200 * L))
    (hm : 200 * L * (1 + normalizedFirstHitCostConstant * exp L) < (m : ℝ)) : IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  have hb (i : Fin P.card) : firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0 :=
    (Nat.nth_monotone Nat.infinite_setOf_prime (show i.val ≤ k by omega)).trans hbound
  obtain ⟨j, hj, havoid⟩ := prime_survivor_of_saturatedHitNormalizedCost P hP r L hL m hb hmain hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

#print axioms isJacobsthalBound_of_saturatedHitNormalizedCost
end Erdos970.FiniteSelberg
