import Submission.WeightedCoreCollision

/-! Exact fibers and finite bounds for the weighted shared-completion source.
Nonempty concentrated survivor populations, rather than bare geometric
collisions, determine the insertion increments. No uniform relative
correlation estimate is asserted. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2000000

lemma cover_avoidClass_iff_survivors_contained (P S : Finset ℕ) (p : ℕ)
    (a : Fin p) (r : Phase P) :
    (∀ x ∈ avoidClass S p a, ∃ q : P, x % q.val = (r q).val) ↔
      ∀ x ∈ populationSurvivors S P r, x % p = a.val := by
  constructor
  · intro h x hx
    by_contra hn
    obtain ⟨q,hq⟩ := h x (mem_filter.mpr ⟨(mem_filter.mp hx).1,hn⟩)
    exact (mem_filter.mp hx).2 q hq
  · intro h x hx
    by_contra hn
    have hsurv : x ∈ populationSurvivors S P r := by
      refine mem_filter.mpr ⟨(mem_filter.mp hx).1,?_⟩
      intro q hq
      exact hn ⟨q,hq⟩
    exact (mem_filter.mp hx).2 (h x hsurv)

/-- The remaining survivor population is nonempty and concentrated in some
single residue class. The residue itself is not specified. -/
noncomputable def populationConcentration (P S : Finset ℕ) (p : ℕ) : ℝ :=
  phaseMean P (fun r => if Concentrated (populationSurvivors S P r) p then 1 else 0)

lemma populationConcentration_nonneg (P S : Finset ℕ) (p : ℕ) :
    0 ≤ populationConcentration P S p := by
  unfold populationConcentration phaseMean
  exact div_nonneg (sum_nonneg (fun r _ => by split_ifs <;> norm_num)) (by positivity)

lemma populationConcentration_le_one (P S : Finset ℕ) (p : ℕ)
    (hP : ∀ q ∈ P, q.Prime) : populationConcentration P S p ≤ 1 := by
  unfold populationConcentration
  have hh := phaseMean_mono P (fun r =>
    show (if Concentrated (populationSurvivors S P r) p then (1 : ℝ) else 0) ≤ 1 by
      split_ifs <;> norm_num)
  rwa [phaseMean_const P hP] at hh

/-- Exact average of the insertion increment. It is the probability of a
nonempty concentrated old population, divided by the new modulus. -/
theorem completionIncrement_mean_concentration (P S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    residueMean p (completionIncrement P S p) = populationConcentration P S p/p := by
  classical
  have hav : residueMean p (fun a => populationCoveredFraction (avoidClass S p a) P) =
      populationCoveredFraction S P+populationConcentration P S p/p := by
    unfold populationCoveredFraction residueMean
    simp_rw [cover_avoidClass_iff_survivors_contained P S p]
    rw [← phaseMean_sum,← phaseMean_div]
    simp_rw [completingResidues_mean _ p hp]
    rw [phaseMean_add,phaseMean_div]
    simp only [population_empty_iff]
    rfl
  unfold completionIncrement
  rw [residueMean_sub,residueMean_const p hp,hav]
  ring

/-- An exact probability interpretation of each increment, before averaging
in the new residue. Already-covered old phases contribute zero. -/
theorem completionIncrement_eq_fiber (P S : Finset ℕ) (p : ℕ) (a : Fin p) :
    completionIncrement P S p a = phaseMean P (fun r =>
      if (populationSurvivors S P r).Nonempty ∧
        (∀ x ∈ populationSurvivors S P r, x % p = a.val) then 1 else 0) := by
  classical
  unfold completionIncrement populationCoveredFraction
  rw [← phaseMean_sub]
  apply congrArg (phaseMean P)
  funext r
  simp only [cover_avoidClass_iff_survivors_contained P S p a r,← population_empty_iff]
  by_cases he : populationSurvivors S P r = ∅
  · simp [he]
  · have hn := nonempty_iff_ne_empty.mpr he
    simp only [he,if_false,sub_zero,hn,true_and]

lemma sum_nonneg_diagonal_le_product {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∑ i, f i*g i) ≤ (∑ i, f i)*(∑ i, g i) := by
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hg j) (mem_univ i)) (hf i)

/-- A useful finite upper bound for the source: the two concentration
probabilities are multiplied, and the new modulus is still charged. -/
theorem completionCollision_le_concentration_product (P S T : Finset ℕ)
    (p : ℕ) (hp : 0 < p) :
    completionCollision P S T p ≤ populationConcentration P S p*populationConcentration P T p/p := by
  have hdiag := sum_nonneg_diagonal_le_product (completionIncrement P S p) (completionIncrement P T p)
    (completionIncrement_nonneg P S p) (completionIncrement_nonneg P T p)
  have hS := completionIncrement_mean_concentration P S p hp
  have hT := completionIncrement_mean_concentration P T p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hSeq : (∑ a, completionIncrement P S p a)=populationConcentration P S p := by
    exact (div_left_inj' hpR.ne').mp hS
  have hTeq : (∑ a, completionIncrement P T p a)=populationConcentration P T p := by
    exact (div_left_inj' hpR.ne').mp hT
  rw [hSeq,hTeq] at hdiag
  exact div_le_div_of_nonneg_right hdiag hpR.le

lemma completionCollision_le_inverse (P S T : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : 0 < p) : completionCollision P S T p ≤ 1/(p : ℝ) := by
  have hh := completionCollision_le_concentration_product P S T p hp
  have hprod : populationConcentration P S p*populationConcentration P T p ≤ 1 := by
    have hS := populationConcentration_le_one P S p hP
    have hT := populationConcentration_le_one P T p hP
    simpa only [one_mul] using mul_le_mul hS hT (populationConcentration_nonneg P T p) (by norm_num)
  exact hh.trans (div_le_div_of_nonneg_right hprod (Nat.cast_nonneg p))

/-- The total positive recursive cost has this coarse reciprocal bound.
It is NOT asserted to be the small relative error required at the endpoint. -/
theorem weightedCollisionCost_le_reciprocal_sum (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (S T : Finset ℕ) :
    weightedCollisionCost ps S T ≤ (ps.map (fun p : ℕ => (1 : ℝ)/(p : ℝ))).sum := by
  induction ps generalizing S T with
  | nil => simp [weightedCollisionCost]
  | cons p ps ih =>
    have hp0 := (hp p (by simp)).pos
    have hps : ∀ q ∈ ps, q.Prime := fun q hq => hp q (by simp [hq])
    have hP : ∀ q ∈ ps.toFinset, q.Prime := fun q hq => hps q (by simpa using hq)
    have hchild := residueMean_mono p (fun a => ih hps (avoidClass S p a) (avoidClass T p a))
    rw [residueMean_const p hp0] at hchild
    have hsrc := completionCollision_le_inverse ps.toFinset S T hP p hp0
    simp only [weightedCollisionCost,List.map_cons,List.sum_cons]
    linarith only [hchild,hsrc]

#print axioms completionIncrement_eq_fiber
#print axioms completionCollision_le_concentration_product
#print axioms weightedCollisionCost_le_reciprocal_sum
end Erdos970.OneHitLogConcavity
