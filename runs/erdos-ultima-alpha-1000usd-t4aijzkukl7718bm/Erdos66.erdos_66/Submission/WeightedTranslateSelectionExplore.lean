import Submission.CharacterTranslateSelectionExplore

/-! Summably weighted simultaneous selection removes dependence on the
number of selected parameter lengths. -/
namespace Erdos66WeightedTranslateSelection
open Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy
open scoped Classical
set_option maxHeartbeats 1800000

lemma reciprocal_square_prefix_bound (N : ℕ) :
    (∑ j∈Finset.range N, (1:ℝ)/((j:ℝ)+1)^2) ≤ 2-2/((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hp : 0<(N:ℝ)+1 := by positivity
    have hq : 0<(N:ℝ)+2 := by positivity
    have hh : (1:ℝ)/((N:ℝ)+1)^2 ≤ 2/((N:ℝ)+1)-2/((N:ℝ)+2) := by
      apply (le_sub_iff_add_le).mpr
      field_simp
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    push_cast
    rw [show (N:ℝ)+1+1=(N:ℝ)+2 by ring]
    linarith

lemma reciprocal_square_prefix_le_two (N : ℕ) :
    (∑ j∈Finset.range N, (1:ℝ)/((j:ℝ)+1)^2) ≤ 2 :=
  (reciprocal_square_prefix_bound N).trans (sub_le_self _ (by positivity))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

 theorem exists_weighted_small_translates (hF : ringChar F ≠ 2) (N : ℕ)
    (U : ℕ → Finset F) (D : Finset F) (hcard : 2*D.card < Fintype.card F) :
    ∃ a, a∉D ∧ ∀ j<N,
      (translatedEnergy (U j) a:ℝ) ≤ 16*((j:ℝ)+1)^2*((U j).card:ℝ)^2 := by
  let f : F → ℝ := fun a ↦ ∑ j∈Finset.range N,
    (translatedEnergy (U j) a:ℝ)/(((j:ℝ)+1)^2*((U j).card:ℝ)^2)
  have hf : ∀ a, 0 ≤ f a := fun a ↦ Finset.sum_nonneg (fun j _ ↦
    div_nonneg (by exact_mod_cast translatedEnergy_nonneg (U j) a) (by positivity))
  have hiavg (j : ℕ) :
      (∑ a : F, (translatedEnergy (U j) a:ℝ)/(((j:ℝ)+1)^2*((U j).card:ℝ)^2)) ≤
        4*(Fintype.card F:ℝ)/((j:ℝ)+1)^2 := by
    rw [←Finset.sum_div]
    have hav : (∑ a : F, (translatedEnergy (U j) a:ℝ)) ≤ 4*(Fintype.card F:ℝ)*((U j).card:ℝ)^2 :=
      by exact_mod_cast average_translated_energy hF (U j)
    by_cases hz : (U j).card=0
    · simp only [hz,Nat.cast_zero,zero_pow (by norm_num : 2≠0),mul_zero,div_zero]
      positivity
    · have hp : 0<((U j).card:ℝ)^2 := by positivity
      have hpos : 0<((j:ℝ)+1)^2 := by positivity
      apply (div_le_iff₀ (mul_pos hpos hp)).mpr
      convert hav using 1
      field_simp
  have hav : (∑ a, f a) ≤ (Fintype.card F:ℝ)*8 := by
    dsimp only [f]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ j∈Finset.range N, 4*(Fintype.card F:ℝ)/((j:ℝ)+1)^2 := Finset.sum_le_sum (fun j _ ↦ hiavg j)
      _ = 4*(Fintype.card F:ℝ)*(∑ j∈Finset.range N, (1:ℝ)/((j:ℝ)+1)^2) := by rw [Finset.mul_sum]; congr 1; funext j; ring
      _ ≤ 4*(Fintype.card F:ℝ)*2 := mul_le_mul_of_nonneg_left (reciprocal_square_prefix_le_two N) (by positivity)
      _ = _ := by ring
  obtain ⟨a,ha,hfa⟩ := exists_small_outside D f 8 hcard hf hav
  refine ⟨a,ha,?_⟩
  intro j hj
  have hsingle : (translatedEnergy (U j) a:ℝ)/(((j:ℝ)+1)^2*((U j).card:ℝ)^2) ≤ f a := by
    apply Finset.single_le_sum (f := fun i ↦ (translatedEnergy (U i) a:ℝ)/(((i:ℝ)+1)^2*((U i).card:ℝ)^2))
      (fun i _ ↦ div_nonneg (by exact_mod_cast translatedEnergy_nonneg (U i) a) (by positivity))
      (Finset.mem_range.mpr hj)
  by_cases hz : (U j).card=0
  · have he : U j=∅ := Finset.card_eq_zero.mp hz
    simp [he,translatedEnergy,translatedFiber,sumFiber]
  · have hp : 0<((j:ℝ)+1)^2*((U j).card:ℝ)^2 := by positivity
    have hh := (div_le_iff₀ hp).mp (hsingle.trans hfa)
    nlinarith only [hh]

 theorem exists_weighted_admissible_intervals (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (H N : ℕ) (hH : 4*H<p) (len : ℕ → ℕ) (hlen : ∀ j<N, len j ≤ H) :
    ∃ a : ZMod p,
      (∀ u∈intervalTranslate p a H, u≠0) ∧
      (∀ u∈intervalTranslate p a H, ∀ v∈intervalTranslate p a H, u+v≠0) ∧
      ∀ j<N, (translatedEnergy (baseInterval p (len j)) a:ℝ) ≤
        16*((j:ℝ)+1)^2*(len j:ℝ)^2 := by
  obtain ⟨a,ha,hE⟩ := exists_weighted_small_translates
    (by simpa only [ZMod.ringChar_zmod_n] using hp) N (fun j ↦ baseInterval p (len j))
    (forbiddenInterval p H) (by
      rw [ZMod.card]
      have hh := forbiddenInterval_card p H
      omega)
  obtain ⟨hzero,hopp⟩ := intervalTranslate_admissible p hp H a ha
  refine ⟨a,hzero,hopp,?_⟩
  intro j hj
  have hc : (baseInterval p (len j)).card=len j := by
    simpa only [intervalTranslate,Finset.card_image_of_injective _ (add_right_injective a)] using
      intervalTranslate_card p a (show len j ≤ p by have := hlen j hj; omega)
  simpa only [hc] using hE j hj

end Erdos66WeightedTranslateSelection
