import Submission.InterceptIncidenceBudgetExplore

/-! A cubic bound for the pointwise collision correction in terms of the
averaged incidence budget. No exclusion of all triple roots is assumed. -/
namespace Erdos66InterceptBudgetPointwise
open Erdos66EdgeTripleBudget Erdos66InterceptEdgePolynomial
  Erdos66InterceptConcurrencyPolynomial Erdos66InterceptGoodTranslation
  Erdos66InterceptIncidenceBudget Erdos66InterceptCollisionIncidence
  Erdos66InterceptCurve Erdos66InterceptCollisionCorrection
  Erdos66InheritedOriginLift Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2400000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def activeEdges (U : Finset F) (a w q t : F) : Finset (F × F) :=
  (properEdges U).filter (fun e ↦ ∃ k, EdgeHit a w q t e k)

lemma active_triples_le_budget (U : Finset F) (a w q t : F) (hw : a+w≠0) :
    tripleMass (activeEdges U a w q t) ≤ budgetAt U a w := by
  let R := activeEdges U a w q t
  have hsub : R ⊆ properEdges U := Finset.filter_subset _ _
  have hpoint (e : F × F) (he : e∈R) (f : F × F) (hf : f∈R)
      (g : F × F) (hg : g∈R) :
      (if Valid e f g then 1 else 0) ≤ rootIndicator a w e f g := by
    by_cases hv : Valid e f g
    · obtain ⟨k,hk⟩ := (Finset.mem_filter.mp he).2
      obtain ⟨l,hl⟩ := (Finset.mem_filter.mp hf).2
      obtain ⟨m,hm⟩ := (Finset.mem_filter.mp hg).2
      have hr := three_hits_root a w q t e f g k l m hw hk hl hm
      simp [rootIndicator,hv,hr]
    · simp [hv]
  change tripleMass R ≤ _
  unfold tripleMass budgetAt
  calc
    _ ≤ ∑ e ∈ R, ∑ f ∈ R, ∑ g ∈ R, rootIndicator a w e f g := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro f hf
      exact Finset.sum_le_sum (fun g hg ↦ hpoint e he f hf g hg)
    _ ≤ ∑ e ∈ R, ∑ f ∈ R, ∑ g ∈ properEdges U, rootIndicator a w e f g := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro f hf
      exact Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ e ∈ R, ∑ f ∈ properEdges U, ∑ g ∈ properEdges U, rootIndicator a w e f g := by
      exact Finset.sum_le_sum (fun e _ ↦ Finset.sum_le_sum_of_subset hsub)
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

lemma active_card_cubic (U : Finset F) (a w q t : F) (hw : a+w≠0) :
    ((activeEdges U a w q t).card-4)^3 ≤ budgetAt U a w :=
  (tripleMass_lower _).trans (active_triples_le_budget U a w q t hw)

lemma collision_curve_active_bound (U : Finset F) (a w q t : F)
    (hU : ∀ u∈translated U a, u≠0) :
    pairCount (collisionSet (translated U a)) (curve (a+w)) (t,q) ≤
      2*(activeEdges U a w q t).card := by
  let S := (collisionSet (translated U a)).filter (fun z ↦ (t,q)-z∈curve (a+w))
  have hs : S ⊆ (activeEdges U a w q t).biUnion (edgePoints a) := by
    intro z hz
    obtain ⟨hz,hc⟩ := Finset.mem_filter.mp hz
    obtain ⟨e,heU,he,heZ⟩ := collision_has_edge U a hU z hz
    have hh := edge_hit_of_membership a w q t e z heZ hc
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨heU,he⟩,⟨z.2,hh⟩⟩,heZ⟩
  change S.card ≤ _
  have hb := biUnion_card_bound (activeEdges U a w q t) (edgePoints a) 2
    (fun e _ ↦ edgePoints_card a e)
  simpa only [Nat.mul_comm] using (Finset.card_le_card hs).trans hb

noncomputable def excessSum (U : Finset F) (a q t : F) : ℕ :=
  ∑ w ∈ U, ((activeEdges U a w q t).card-4)

lemma excessSum_cubic (U : Finset F) (a q t : F) (hU : ∀ w∈U, a+w≠0) :
    (excessSum U a q t)^3 ≤ U.card^2*budget U a := by
  have hh := pow_sum_le_card_mul_sum_pow
    (s := U) (f := fun w ↦ (activeEdges U a w q t).card-4)
    (fun _ _ ↦ Nat.zero_le _) 2
  change (excessSum U a q t)^3 ≤ _ at hh
  apply hh.trans
  apply Nat.mul_le_mul_left
  exact Finset.sum_le_sum (fun w hw ↦ active_card_cubic U a w q t (hU w hw))

lemma collision_union_budget_bound (U : Finset F) (a q t : F)
    (hU : ∀ u∈translated U a, u≠0) :
    pairCount (collisionSet (translated U a)) (curveUnion (translated U a)) (t,q) ≤
      8*U.card+2*excessSum U a q t := by
  have hh := Erdos66ParabolaRepair.pairCount_biUnion_right_le
    (translated U a) curve (collisionSet (translated U a)) (t,q)
  have hs : (∑ u∈translated U a,
      pairCount (collisionSet (translated U a)) (curve u) (t,q)) =
      ∑ w∈U, pairCount (collisionSet (translated U a)) (curve (a+w)) (t,q) := by
    rw [translated,Finset.sum_image]
    intro x hx y hy hxy
    exact add_left_cancel hxy
  rw [hs] at hh
  calc
    _ ≤ ∑ w∈U, pairCount (collisionSet (translated U a)) (curve (a+w)) (t,q) := hh
    _ ≤ ∑ w∈U, (8+2*((activeEdges U a w q t).card-4)) := by
      apply Finset.sum_le_sum
      intro w hw
      have hc := collision_curve_active_bound U a w q t hU
      omega
    _ = _ := by simp [excessSum,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]

noncomputable def correction (U : Finset F) (a : F) (z : F × F) : ℕ :=
  2*pairCount (curveUnion (translated U a)) (collisionSet (translated U a)) z+
    pairCount (collisionSet (translated U a)) (collisionSet (translated U a)) z

lemma correction_bound (U : Finset F) (a q t : F)
    (hU : ∀ u∈translated U a, u≠0) :
    correction U a (t,q) ≤ 24*U.card+6*excessSum U a q t := by
  have hc := collision_union_budget_bound U a q t hU
  have hd : pairCount (collisionSet (translated U a)) (collisionSet (translated U a)) (t,q) ≤
      pairCount (collisionSet (translated U a)) (curveUnion (translated U a)) (t,q) := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx,collision_subset_union _ hzx⟩
  unfold correction
  rw [pairCount_comm (curveUnion _) (collisionSet _)]
  omega

/-- Cubic pointwise correction; the budget is shared by all targets. -/
theorem correction_cubic (U : Finset F) (a : F)
    (hU : ∀ u∈translated U a, u≠0) (z : F × F) :
    (correction U a z-24*U.card)^3 ≤ 216*U.card^2*budget U a := by
  obtain ⟨t,q⟩ := z
  have hh := correction_bound U a q t hU
  have hs : correction U a (t,q)-24*U.card ≤ 6*excessSum U a q t := by omega
  have hc := excessSum_cubic U a q t (fun w hw ↦
    hU (a+w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
  calc
    _ ≤ (6*excessSum U a q t)^3 := Nat.pow_le_pow_left hs 3
    _ = 216*(excessSum U a q t)^3 := by ring
    _ ≤ 216*(U.card^2*budget U a) := Nat.mul_le_mul_left _ hc
    _ = _ := by ring

/-- The selector gives a uniform pointwise polynomial bound, rather than
merely an averaged error estimate. -/
theorem exists_low_energy_pointwise (hF : ringChar F≠2) (U : Finset F)
    (hU : 0 < U.card) (hsize : 2*U.card^2 < Fintype.card F) :
    ∃ a : F, a∉oppositeForbidden U ∧
      (Erdos66TranslatedCharacterEnergy.translatedEnergy U a : ℝ) ≤ 16*(U.card : ℝ)^2 ∧
      ∀ z : F × F, Fintype.card F*(correction U a z-24*U.card)^3 ≤ 6912*U.card^9 := by
  obtain ⟨a,ha,hE,hP⟩ := exists_low_energy_budget hF U hU hsize
  obtain ⟨hz,_⟩ := outside_opposite (Ring.two_ne_zero hF) U a ha
  have hzero : ∀ u∈translated U a, u≠0 := by
    intro u hu
    change u∈U.image (fun w ↦ a+w) at hu
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
    exact hz w hw
  have hb : Fintype.card F*budget U a ≤ 32*U.card^7 := by exact_mod_cast hP
  refine ⟨a,ha,hE,fun z ↦ ?_⟩
  calc
    _ ≤ Fintype.card F*(216*U.card^2*budget U a) :=
      Nat.mul_le_mul_left _ (correction_cubic U a hzero z)
    _ = 216*U.card^2*(Fintype.card F*budget U a) := by ring
    _ ≤ 216*U.card^2*(32*U.card^7) := Nat.mul_le_mul_left _ hb
    _ = _ := by ring

end Erdos66InterceptBudgetPointwise
