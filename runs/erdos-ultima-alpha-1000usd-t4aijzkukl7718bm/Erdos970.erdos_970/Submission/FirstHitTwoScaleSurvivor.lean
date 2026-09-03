import Submission.FirstHitTwoScaleMain
import Submission.FirstHitTwoScaleCost

/-! Unconditional survivor transfer using the normalizer-sensitive first-hit
remainder. The required main-term slack is displayed explicitly. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma twoScale_reference_main_le (k : ℕ) (L : ℝ)
    (hbound : ∀ i : Fin k, firstPrimeList k i ≤ saturatedHitPrimeCut L 0) :
    (∑ i : Fin k, (1/(firstPrimeList k i : ℝ)) /
      normalizer (fun j => 1/(firstPrimeList k j : ℝ))
        (priorDivisorSupport (firstPrimeList k) i (twoScaleCutoff L (firstPrimeList k i)))) ≤
      twoScaleMainSum L := by
  simp_rw [reference_prior_normalizer]
  have hsub : univ.image (firstPrimeList k) ⊆ (saturatedHitPrimeCut L 0+1).primesBelow := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := mem_image.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨firstPrimeList_prime k i,hbound i⟩
  rw [← sum_image (f := fun p : ℕ => (1/(p : ℝ))/primeNormalizer p.primesBelow (twoScaleCutoff L p))
    (s := univ) (firstPrimeList_strictMono k).injective.injOn]
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _
  have hG := primeNormalizer_ge_one p.primesBelow (twoScaleCutoff L p)
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) (twoScaleCutoff_pos L p)
  positivity

/-- A first-hit certificate with a fixed absolute remainder bound, transferred
from the initial prime list to an arbitrary prime set. -/
theorem prime_survivor_of_twoScale (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (L : ℝ) (hL : 100 ≤ L) (m : ℕ)
    (hbound : ∀ i : Fin P.card, firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0)
    (hmain : twoScaleMainSum L ≤ 1 - 1 / (400 * L))
    (hm : 400 * L * (1 + twoScaleCostConstant * exp L/L^2) < (m : ℝ)) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  have hL0 : 0 < L := by linarith
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  let q : Fin P.card → ℝ := fun i => 1 / (p i : ℝ)
  let q' : Fin P.card → ℝ := fun i => 1 / (firstPrimeList P.card i : ℝ)
  let D (i : Fin P.card) := priorDivisorSupport (firstPrimeList P.card) i
    (twoScaleCutoff L (firstPrimeList P.card i))
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
    priorDivisorSupport_nonempty _ _ _ (twoScaleCutoff_pos L _)
  have hD (i : Fin P.card) : ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i :=
    priorDivisorSupport_downward _ (fun j => (firstPrimeList_prime P.card j).one_lt.le) _ _
  have hprior (i : Fin P.card) : ∀ T ∈ D i, ∀ j ∈ T, j < i := priorDivisorSupport_prior _ _ _
  have hmean := (twoScale_reference_main_le P.card L hbound).trans hmain
  have hcost := twoScale_reference_cost P.card L hL hbound
  have hobjective : (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) +
      1 + (∑ i, kernelCost q' (canonicalOrthogonal q' (D i)) ^ 2) < m := by
    have hh := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg m)
    have hmc : 1 + twoScaleCostConstant * exp L/L^2 < (m : ℝ) / (400 * L) := by
      apply (lt_div_iff₀ (by positivity : 0 < 400 * L)).mpr
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
theorem isJacobsthalBound_of_twoScale (k : ℕ) (L : ℝ) (hL : 100 ≤ L) (m : ℕ)
    (hbound : Nat.nth Nat.Prime k ≤ saturatedHitPrimeCut L 0)
    (hmain : twoScaleMainSum L ≤ 1 - 1 / (400 * L))
    (hm : 400 * L * (1 + twoScaleCostConstant * exp L/L^2) < (m : ℝ)) : IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  have hb (i : Fin P.card) : firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0 :=
    (Nat.nth_monotone Nat.infinite_setOf_prime (show i.val ≤ k by omega)).trans hbound
  obtain ⟨j, hj, havoid⟩ := prime_survivor_of_twoScale P hP r L hL m hb hmain hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

#print axioms isJacobsthalBound_of_twoScale
end Erdos970.FiniteSelberg
