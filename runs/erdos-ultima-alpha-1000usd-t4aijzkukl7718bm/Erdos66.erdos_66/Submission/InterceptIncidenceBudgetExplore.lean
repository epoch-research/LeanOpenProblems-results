import Submission.EdgeTripleBudgetExplore

/-! An averaged incidence budget replaces exclusion of every polynomial root.
This file only supplies finite-field estimates and a simultaneous selector. -/
namespace Erdos66InterceptIncidenceBudget
open Polynomial Erdos66EdgeTripleBudget Erdos66InterceptEdgePolynomial
  Erdos66InterceptConcurrencyPolynomial Erdos66InterceptGoodTranslation
  Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy
open scoped Classical
set_option maxHeartbeats 2200000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def properEdges (U : Finset F) : Finset (F × F) :=
  (edges U).filter (fun e ↦ e.1≠e.2)

noncomputable def rootIndicator (a w : F) (e f g : F × F) : ℕ :=
  if Valid e f g ∧ (concurrencyPolynomial w e f g).eval a=0 then 1 else 0

noncomputable def budgetAt (U : Finset F) (a w : F) : ℕ :=
  ∑ e ∈ properEdges U, ∑ f ∈ properEdges U, ∑ g ∈ properEdges U,
    rootIndicator a w e f g

noncomputable def budget (U : Finset F) (a : F) : ℕ :=
  ∑ w ∈ U, budgetAt U a w

omit [Field F] [Fintype F] in
lemma properEdges_card (U : Finset F) : (properEdges U).card ≤ U.card^2 := by
  have hh := Finset.card_filter_le (edges U) (fun e ↦ e.1≠e.2)
  simpa only [edges,Finset.card_product,pow_two] using hh

lemma rootIndicator_sum (h2 : (2 : F)≠0) (w : F) (e f g : F × F)
    (he : e.1≠e.2) : (∑ a : F, rootIndicator a w e f g) ≤ 8 := by
  by_cases hv : Valid e f g
  · have hp := concurrencyPolynomial_ne_zero h2 w e f g he hv.1 hv.2.1 hv.2.2
    have hs : (Finset.univ.filter (fun a ↦ (concurrencyPolynomial w e f g).eval a=0)) ⊆
        (concurrencyPolynomial w e f g).roots.toFinset := by
      intro a ha
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp ha).2)
    have hh := (Finset.card_le_card hs).trans (polynomial_root_card w e f g)
    simpa only [rootIndicator,hv,true_and,Finset.sum_boole,Nat.cast_id] using hh
  · simp [rootIndicator,hv]

lemma budgetAt_sum (h2 : (2 : F)≠0) (U : Finset F) (w : F) :
    (∑ a : F, budgetAt U a w) ≤ 8*U.card^6 := by
  have hs : (∑ a : F, budgetAt U a w) =
      ∑ e ∈ properEdges U, ∑ f ∈ properEdges U, ∑ g ∈ properEdges U,
        ∑ a : F, rootIndicator a w e f g := by
    unfold budgetAt
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.sum_comm]
  rw [hs]
  calc
    _ ≤ ∑ _e ∈ properEdges U, ∑ _f ∈ properEdges U, ∑ _g ∈ properEdges U, 8 := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro f hf
      apply Finset.sum_le_sum
      intro g hg
      exact rootIndicator_sum h2 w e f g (Finset.mem_filter.mp he).2
    _ = 8*(properEdges U).card^3 := by simp; ring
    _ ≤ 8*(U.card^2)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (properEdges_card U) 3)
    _ = _ := by ring

lemma budget_sum (h2 : (2 : F)≠0) (U : Finset F) :
    (∑ a : F, budget U a) ≤ 8*U.card^7 := by
  unfold budget
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _w ∈ U, 8*U.card^6 := Finset.sum_le_sum (fun w _ ↦ budgetAt_sum h2 U w)
    _ = _ := by simp; ring

/-- One translation has both a small energy and a small incidence budget.
Only opposite-pair translations are removed, at the explicit cost `2 h²<p`. -/
theorem exists_low_energy_budget (hF : ringChar F≠2) (U : Finset F)
    (hU : 0 < U.card) (hsize : 2*U.card^2 < Fintype.card F) :
    ∃ a : F, a∉oppositeForbidden U ∧
      (translatedEnergy U a : ℝ) ≤ 16*(U.card : ℝ)^2 ∧
      (Fintype.card F : ℝ)*(budget U a : ℝ) ≤ 32*(U.card : ℝ)^7 := by
  let h : ℝ := U.card
  let p : ℝ := Fintype.card F
  have hh : 0 < h := by dsimp [h]; exact_mod_cast hU
  have hp : 0 < p := by dsimp [p]; exact_mod_cast Fintype.card_pos
  let f : F → ℝ := fun a ↦ (translatedEnergy U a : ℝ)/(4*h^2)+p*(budget U a : ℝ)/(8*h^7)
  have hf (a : F) : 0 ≤ f a :=
    add_nonneg (div_nonneg (by exact_mod_cast translatedEnergy_nonneg U a) (by positivity))
      (by positivity)
  have hE : (∑ a : F, (translatedEnergy U a : ℝ)) ≤ 4*p*h^2 := by
    dsimp [p,h]
    exact_mod_cast average_translated_energy hF U
  have hP : (∑ a : F, (budget U a : ℝ)) ≤ 8*h^7 := by
    dsimp [h]
    exact_mod_cast budget_sum (Ring.two_ne_zero hF) U
  have hsum : (∑ a : F, f a) ≤ p*2 := by
    simp only [f,Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum]
    have h1 : (∑ a : F, (translatedEnergy U a : ℝ))/(4*h^2) ≤ p := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [hE]
    have h2 : p*(∑ a : F, (budget U a : ℝ))/(8*h^7) ≤ p := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hP hp.le]
    linarith
  obtain ⟨a,ha,hfa⟩ := exists_small_outside (oppositeForbidden U) f 2
    (by have hc := oppositeForbidden_card U; omega) hf hsum
  have h1 : (translatedEnergy U a : ℝ)/(4*h^2) ≤ f a := le_add_of_nonneg_right
    (show 0 ≤ p*(budget U a : ℝ)/(8*h^7) by positivity)
  have h2 : p*(budget U a : ℝ)/(8*h^7) ≤ f a := le_add_of_nonneg_left
    (show 0 ≤ (translatedEnergy U a : ℝ)/(4*h^2) from
      div_nonneg (by exact_mod_cast translatedEnergy_nonneg U a) (by positivity))
  have he : (translatedEnergy U a : ℝ)/(4*h^2) ≤ 4 := by
    exact h1.trans (by simpa only [show (2:ℝ)*2=4 by norm_num] using hfa)
  have hb : p*(budget U a : ℝ)/(8*h^7) ≤ 4 := by
    exact h2.trans (by simpa only [show (2:ℝ)*2=4 by norm_num] using hfa)
  refine ⟨a,ha,?_,?_⟩
  · have he' := (div_le_iff₀ (by positivity : 0 < 4*h^2)).mp he
    dsimp [h] at he'
    nlinarith
  · have hb' := (div_le_iff₀ (by positivity : 0 < 8*h^7)).mp hb
    dsimp [h,p] at hb'
    nlinarith

end Erdos66InterceptIncidenceBudget
