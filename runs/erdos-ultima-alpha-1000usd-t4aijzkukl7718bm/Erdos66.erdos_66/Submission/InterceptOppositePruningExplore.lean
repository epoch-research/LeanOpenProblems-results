import Submission.InterceptIncidenceBudgetExplore

/-! Pruning opposite parameters, with the number removed charged to an
averagable incidence count rather than to a forbidden translation set. -/
namespace Erdos66InterceptOppositePruning
open Erdos66InterceptGoodTranslation Erdos66InterceptIncidenceBudget
  Erdos66InheritedOriginLift Erdos66CharacterTranslateSelection
  Erdos66TranslatedCharacterEnergy
open scoped Classical
set_option maxHeartbeats 2400000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def oppositeCount (U : Finset F) (a : F) : ℕ :=
  ∑ u∈U, ∑ v∈U, if a=-(u+v)/2 then 1 else 0

noncomputable def pruned (U : Finset F) (a : F) : Finset F :=
  U.filter (fun u ↦ ∀ v∈U, a≠-(u+v)/2)

lemma pruned_subset (U : Finset F) (a : F) : pruned U a ⊆ U := Finset.filter_subset _ _

lemma oppositeCount_sum (U : Finset F) : (∑ a : F, oppositeCount U a)=U.card^2 := by
  unfold oppositeCount
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ)]
  simp [pow_two]

lemma pruned_card_loss (U : Finset F) (a : F) :
    U.card ≤ (pruned U a).card+oppositeCount U a := by
  have he := @Finset.card_filter_add_card_filter_not _ U
    (fun u ↦ ∀ v∈U, a≠-(u+v)/2) _ _
  have hb : (U.filter (fun u ↦ ¬∀ v∈U, a≠-(u+v)/2)).card ≤ oppositeCount U a := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro u hu
    by_cases hh : ∀ v∈U, a≠-(u+v)/2
    · rw [if_neg (not_not_intro hh)]
      exact Nat.zero_le _
    · rw [if_pos hh]
      push_neg at hh
      obtain ⟨v,hv,hv'⟩ := hh
      have hs := Finset.single_le_sum
        (f := fun v ↦ if a=-(u+v)/2 then (1:ℕ) else 0)
        (fun _ _ ↦ Nat.zero_le _) hv
      simpa only [hv',if_true] using hs
  change (pruned U a).card+_ = U.card at he
  omega

lemma pruned_admissible (h2 : (2 : F)≠0) (U : Finset F) (a : F) :
    (∀u∈translated (pruned U a) a, u≠0) ∧
      ∀u∈translated (pruned U a) a,∀v∈translated (pruned U a) a,u+v≠0 := by
  have hpair (u : F) (hu : u∈pruned U a) (v : F) (hv : v∈U) :
      (a+u)+(a+v)≠0 := by
    intro hz
    apply (Finset.mem_filter.mp hu).2 v hv
    apply (eq_div_iff h2).mpr
    linear_combination hz
  have hz (u : F) (hu : u∈pruned U a) : a+u≠0 := by
    intro he
    exact hpair u hu u (pruned_subset U a hu) (by rw [he]; simp)
  constructor
  · intro u hu
    change u∈(pruned U a).image (fun w ↦ a+w) at hu
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
    exact hz w hw
  · intro u hu v hv
    change u∈(pruned U a).image (fun w ↦ a+w) at hu
    change v∈(pruned U a).image (fun w ↦ a+w) at hv
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,rfl⟩ := Finset.mem_image.mp hv
    exact hpair u0 hu0 v0 (pruned_subset U a hv0)

omit [Field F] [Fintype F] in
lemma properEdges_mono {U V : Finset F} (h : V⊆U) : properEdges V ⊆ properEdges U := by
  intro e he
  obtain ⟨he,hn⟩ := Finset.mem_filter.mp he
  obtain ⟨he1,he2⟩ := Finset.mem_product.mp he
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h he1,h he2⟩,hn⟩

omit [Fintype F] in
lemma budgetAt_mono {U V : Finset F} (h : V⊆U) (a w : F) : budgetAt V a w ≤ budgetAt U a w := by
  have hs := properEdges_mono h
  unfold budgetAt
  calc
    _ ≤ ∑e∈properEdges V,∑f∈properEdges V,∑g∈properEdges U,rootIndicator a w e f g :=
      Finset.sum_le_sum (fun e _ ↦ Finset.sum_le_sum (fun f _ ↦ Finset.sum_le_sum_of_subset hs))
    _ ≤ ∑e∈properEdges V,∑f∈properEdges U,∑g∈properEdges U,rootIndicator a w e f g :=
      Finset.sum_le_sum (fun e _ ↦ Finset.sum_le_sum_of_subset hs)
    _ ≤ _ := Finset.sum_le_sum_of_subset hs

omit [Fintype F] in
lemma budget_mono {U V : Finset F} (h : V⊆U) (a : F) : budget V a ≤ budget U a := by
  unfold budget
  exact (Finset.sum_le_sum (fun w _ ↦ budgetAt_mono h a w)).trans
    (Finset.sum_le_sum_of_subset h)

/-- No field-size inequality is needed for this selector. Opposite labels
are counted, not excluded; they can subsequently be removed and restored
only on the old row. -/
theorem exists_energy_budget_opposites (hF : ringChar F≠2) (U : Finset F)
    (hU : 0 < U.card) :
    ∃ a : F, (translatedEnergy U a : ℝ) ≤ 12*(U.card : ℝ)^2 ∧
      (Fintype.card F : ℝ)*(budget U a : ℝ) ≤ 24*(U.card : ℝ)^7 ∧
      (Fintype.card F : ℝ)*(oppositeCount U a : ℝ) ≤ 3*(U.card : ℝ)^2 := by
  let h : ℝ := U.card
  let p : ℝ := Fintype.card F
  have hh : 0 < h := by dsimp [h]; exact_mod_cast hU
  have hp : 0 < p := by dsimp [p]; exact_mod_cast Fintype.card_pos
  let f : F → ℝ := fun a ↦ (translatedEnergy U a : ℝ)/(4*h^2)+
    p*(budget U a : ℝ)/(8*h^7)+p*(oppositeCount U a : ℝ)/h^2
  have hEn (a : F) : 0 ≤ (translatedEnergy U a : ℝ)/(4*h^2) :=
    div_nonneg (by exact_mod_cast translatedEnergy_nonneg U a) (by positivity)
  have hBn (a : F) : 0 ≤ p*(budget U a : ℝ)/(8*h^7) := by positivity
  have hOn (a : F) : 0 ≤ p*(oppositeCount U a : ℝ)/h^2 := by positivity
  have hE : (∑a : F,(translatedEnergy U a : ℝ)) ≤ 4*p*h^2 := by
    dsimp [p,h]
    exact_mod_cast average_translated_energy hF U
  have hB : (∑a : F,(budget U a : ℝ)) ≤ 8*h^7 := by
    dsimp [h]
    exact_mod_cast budget_sum (Ring.two_ne_zero hF) U
  have hO : (∑a : F,(oppositeCount U a : ℝ)) = h^2 := by
    dsimp [h]
    exact_mod_cast oppositeCount_sum U
  have hsum : (∑a : F,f a) ≤ p*3 := by
    simp only [f,Finset.sum_add_distrib,←Finset.sum_div,←Finset.mul_sum]
    have h1 : (∑a : F,(translatedEnergy U a : ℝ))/(4*h^2) ≤ p := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hE]
    have h2 : p*(∑a : F,(budget U a : ℝ))/(8*h^7) ≤ p := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hB hp.le]
    have h3 : p*(∑a : F,(oppositeCount U a : ℝ))/h^2 = p := by
      rw [hO,mul_div_cancel_right₀ _ (ne_of_gt (sq_pos_of_pos hh))]
    linarith
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hminsum := Finset.sum_le_sum (s := Finset.univ) (fun b hb ↦ hmin b hb)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hminsum
  have hfa : f a ≤ 3 := by change p*f a ≤ _ at hminsum; nlinarith
  have he : (translatedEnergy U a : ℝ)/(4*h^2) ≤ 3 := by
    dsimp [f] at hfa
    linarith [hBn a,hOn a]
  have hb : p*(budget U a : ℝ)/(8*h^7) ≤ 3 := by
    dsimp [f] at hfa
    linarith [hEn a,hOn a]
  have ho : p*(oppositeCount U a : ℝ)/h^2 ≤ 3 := by
    dsimp [f] at hfa
    linarith [hEn a,hBn a]
  have he' := (div_le_iff₀ (by positivity : 0 < 4*h^2)).mp he
  have hb' := (div_le_iff₀ (by positivity : 0 < 8*h^7)).mp hb
  have ho' := (div_le_iff₀ (by positivity : 0 < h^2)).mp ho
  refine ⟨a,?_,?_,?_⟩ <;> dsimp [p,h] at he' hb' ho' <;> nlinarith

end Erdos66InterceptOppositePruning
