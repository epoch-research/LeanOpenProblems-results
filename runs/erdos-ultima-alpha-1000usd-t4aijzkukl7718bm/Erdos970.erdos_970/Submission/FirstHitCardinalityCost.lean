import Submission.FirstHitSaturatedSurvivor
import Submission.PrimeSetMertens

/-! Cardinality-sensitive first-hit cost. The prime reciprocal sum is kept
at its logarithmic-logarithmic scale instead of replaced by a harmonic sum.
This does not change the first-hit base exponent 54/25. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma saturated_reference_prior_cost_budget (t k : ℕ) (htk : t ≤ k)
    (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ i : Fin t, firstPrimeList t i ≤ saturatedHitPrimeCut L 0) :
    (∑ i : Fin t, ((priorDivisorSupport (firstPrimeList t) i
      (firstHitCutoff L (firstPrimeList t i))).card : ℝ)^2) ≤
      4*exp L*(log (log ((k : ℝ)+2)) + WeightedMertens.reciprocalConstant) := by
  let S := (univ : Finset (Fin t)).image (firstPrimeList t)
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact firstPrimeList_prime t i
  have hSc : S.card ≤ k := by
    exact (card_image_le.trans_eq (by simp)).trans htk
  have hrec := WeightedMertens.prime_set_reciprocal_le S hSp k hSc
  have hsum : (∑ i : Fin t, 1/(firstPrimeList t i : ℝ)) ≤
      log (log ((k : ℝ)+2)) + WeightedMertens.reciprocalConstant := by
    dsimp only [S] at hrec
    rw [sum_image (firstPrimeList_strictMono t).injective.injOn] at hrec
    simpa only [one_div] using hrec
  have hZL := (saturatedHit_top_log_bound L hL).2
  calc
    _ ≤ ∑ i : Fin t, (firstHitCutoff L (firstPrimeList t i) : ℝ)^2 := by
      apply sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast priorDivisorSupport_card_le _ (firstPrimeList_prime t)
        (firstPrimeList_strictMono t).injective i (firstHitCutoff L (firstPrimeList t i))
    _ ≤ ∑ i : Fin t, 4*exp L/(firstPrimeList t i : ℝ) := by
      apply sum_le_sum
      intro i hi
      have hlog := log_le_log (show (0 : ℝ) < firstPrimeList t i by exact_mod_cast (firstPrimeList_prime t i).pos)
        (show (firstPrimeList t i : ℝ) ≤ saturatedHitPrimeCut L 0 by exact_mod_cast hbound i)
      convert firstHitCutoff_sq_le L (firstPrimeList t i) (firstPrimeList_prime t i).pos (by linarith) using 1 <;> ring
    _ = 4*exp L*∑ i : Fin t, 1/(firstPrimeList t i : ℝ) := by rw [mul_sum]; congr 1; funext i; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- A first-hit certificate with a fixed absolute remainder bound, transferred
from the initial prime list to an arbitrary prime set. -/
theorem prime_survivor_of_saturatedHitCardCost (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hPk : P.card ≤ k) (r : ℕ → ℕ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hbound : ∀ i : Fin P.card, firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0)
    (hmain : saturatedHitMainSum L ≤ 1 - 1 / (200 * L))
    (hm : 200 * L * (1 + 4 * exp L * (log (log ((k : ℝ)+2)) + WeightedMertens.reciprocalConstant)) < (m : ℝ)) :
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
  have hcost := saturated_reference_prior_cost_budget P.card k hPk L hL.le hbound
  have hobjective : (m : ℝ) * (∑ i, q' i / normalizer q' (D i)) +
      1 + (∑ i, ((D i).card : ℝ) ^ 2) < m := by
    have hh := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg m)
    have hmc : 1 + 4 * exp L * (log (log ((k : ℝ)+2)) + WeightedMertens.reciprocalConstant) < (m : ℝ) / (200 * L) := by
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
theorem isJacobsthalBound_of_saturatedHitCardCost (k : ℕ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hbound : Nat.nth Nat.Prime k ≤ saturatedHitPrimeCut L 0)
    (hmain : saturatedHitMainSum L ≤ 1 - 1 / (200 * L))
    (hm : 200 * L * (1 + 4 * exp L * (log (log ((k : ℝ)+2)) + WeightedMertens.reciprocalConstant)) < (m : ℝ)) : IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  have hb (i : Fin P.card) : firstPrimeList P.card i ≤ saturatedHitPrimeCut L 0 :=
    (Nat.nth_monotone Nat.infinite_setOf_prime (show i.val ≤ k by omega)).trans hbound
  obtain ⟨j, hj, havoid⟩ := prime_survivor_of_saturatedHitCardCost P hP k hPk r L hL m hb hmain hm
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact havoid p hp hjp

#print axioms saturated_reference_prior_cost_budget
#print axioms isJacobsthalBound_of_saturatedHitCardCost
end Erdos970.FiniteSelberg
