import Submission.TranslatedCharacterEnergyExplore

/-! Simultaneous small energies after excluding a set of bad translations.
These statements are finite-field selection results, not an infinite basis. -/
namespace Erdos66CharacterTranslateSelection
open Erdos66TranslatedCharacterEnergy
open scoped Classical

lemma exists_small_outside {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset α) (f : α → ℝ) (B : ℝ)
    (hcard : 2*D.card < Fintype.card α) (hf : ∀ a, 0 ≤ f a)
    (hsum : (∑ a, f a) ≤ (Fintype.card α : ℝ)*B) :
    ∃ a, a ∉ D ∧ f a ≤ 2*B := by
  let T := Finset.univ \ D
  have hc : T.card = Fintype.card α-D.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),Finset.card_univ]
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image T f hT
  have hminsum := Finset.sum_le_sum (s := T) (fun b hb ↦ hmin b hb)
  simp only [Finset.sum_const,nsmul_eq_mul] at hminsum
  have hsub : (∑ b ∈ T, f b) ≤ ∑ b, f b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ ↦ hf b)
  have hmass : (Fintype.card α : ℝ) < 2*T.card := by exact_mod_cast (show Fintype.card α < 2*T.card by omega)
  have hB : 0 ≤ B := by
    have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast (show 0 < Fintype.card α by omega)
    have hz : 0 ≤ (Fintype.card α : ℝ)*B :=
      (Finset.sum_nonneg (fun b _ ↦ hf b)).trans hsum
    exact nonneg_of_mul_nonneg_right hz hpos
  refine ⟨a,(Finset.mem_sdiff.mp ha).2,?_⟩
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hmul := mul_le_mul_of_nonneg_right hmass.le hB
  nlinarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma translatedEnergy_nonneg (U : Finset F) (a : F) : 0 ≤ translatedEnergy U a :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The common translation controls any finite list of energies. The cost is
linear in the number of selected sets, independent of the field size. -/
theorem exists_simultaneous_small_translates {ι : Type*}
    (hF : ringChar F ≠ 2) (S : Finset ι) (U : ι → Finset F)
    (D : Finset F) (hcard : 2*D.card < Fintype.card F) :
    ∃ a, a ∉ D ∧ ∀ i ∈ S,
      (translatedEnergy (U i) a : ℝ) ≤ 8*S.card*((U i).card : ℝ)^2 := by
  let f : F → ℝ := fun a ↦ ∑ i ∈ S,
    (translatedEnergy (U i) a : ℝ)/((U i).card : ℝ)^2
  have hf : ∀ a, 0 ≤ f a := fun a ↦ Finset.sum_nonneg (fun i _ ↦
    div_nonneg (by exact_mod_cast translatedEnergy_nonneg (U i) a) (sq_nonneg _))
  have hiavg (i : ι) :
      (∑ a : F, (translatedEnergy (U i) a : ℝ)/((U i).card : ℝ)^2) ≤
        4*(Fintype.card F : ℝ) := by
    rw [← Finset.sum_div]
    have hav : (∑ a : F, (translatedEnergy (U i) a : ℝ)) ≤
        4*(Fintype.card F : ℝ)*((U i).card : ℝ)^2 := by
      exact_mod_cast average_translated_energy hF (U i)
    by_cases hz : (U i).card=0
    · simp [hz]
    · have hp : (0 : ℝ) < ((U i).card : ℝ)^2 := by positivity
      exact (div_le_iff₀ hp).mpr hav
  have hav : (∑ a, f a) ≤ (Fintype.card F : ℝ)*(4*S.card) := by
    dsimp [f]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i ∈ S, 4*(Fintype.card F : ℝ) := Finset.sum_le_sum (fun i _ ↦ hiavg i)
      _ = _ := by simp; ring
  obtain ⟨a,ha,hfa⟩ := exists_small_outside D f (4*S.card) hcard hf hav
  refine ⟨a,ha,fun i hi ↦ ?_⟩
  have hsingle : (translatedEnergy (U i) a : ℝ)/((U i).card : ℝ)^2 ≤ f a := by
    apply Finset.single_le_sum (f := fun j ↦ (translatedEnergy (U j) a : ℝ)/((U j).card : ℝ)^2) _ hi
    intro j hj
    exact div_nonneg (by exact_mod_cast translatedEnergy_nonneg (U j) a) (sq_nonneg _)
  by_cases hz : (U i).card=0
  · have he : U i=∅ := Finset.card_eq_zero.mp hz
    simp [he,translatedEnergy,translatedFiber,sumFiber]
  · have hp : (0 : ℝ) < ((U i).card : ℝ)^2 := by positivity
    have hh := (div_le_iff₀ hp).mp (hsingle.trans hfa)
    nlinarith

noncomputable def baseInterval (p h : ℕ) : Finset (ZMod p) :=
  (Finset.range h).image Nat.cast

noncomputable def intervalTranslate (p : ℕ) (a : ZMod p) (h : ℕ) : Finset (ZMod p) :=
  (baseInterval p h).image (fun x ↦ a+x)

noncomputable def forbiddenInterval (p H : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Finset.range (2*H)).image (fun k : ℕ ↦ -(k : ZMod p)/2)

lemma forbiddenInterval_card (p H : ℕ) [Fact p.Prime] : (forbiddenInterval p H).card ≤ 2*H := by
  unfold forbiddenInterval
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

lemma intervalTranslate_mono (p : ℕ) (a : ZMod p) : Monotone (intervalTranslate p a) := by
  intro h k hhk
  exact Finset.image_subset_image (Finset.image_subset_image (Finset.range_mono hhk))

lemma intervalTranslate_card (p : ℕ) [NeZero p] (a : ZMod p) {h : ℕ} (hh : h ≤ p) :
    (intervalTranslate p a h).card = h := by
  rw [intervalTranslate,Finset.card_image_of_injective _ (add_right_injective a)]
  unfold baseInterval
  rw [Finset.card_image_of_injOn,Finset.card_range]
  intro i hi j hj hij
  have hi' : i < p := (Finset.mem_range.mp hi).trans_le hh
  have hj' : j < p := (Finset.mem_range.mp hj).trans_le hh
  have hv := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt hi',ZMod.val_natCast_of_lt hj'] using hv

lemma intervalTranslate_admissible (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (H : ℕ) (a : ZMod p) (ha : a ∉ forbiddenInterval p H) :
    (∀ u ∈ intervalTranslate p a H, u ≠ 0) ∧
    ∀ u ∈ intervalTranslate p a H, ∀ v ∈ intervalTranslate p a H, u+v ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hn (i j : ℕ) (hi : i < H) (hj : j < H) : a+(i : ZMod p)+(a+(j : ZMod p)) ≠ 0 := by
    intro he
    apply ha
    apply Finset.mem_image.mpr
    refine ⟨i+j,Finset.mem_range.mpr (by omega),?_⟩
    apply (div_eq_iff htwo).mpr
    push_cast
    linear_combination -he
  constructor
  · intro u hu
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    intro he
    exact hn i i (Finset.mem_range.mp hi) (Finset.mem_range.mp hi) (by rw [he]; simp)
  · intro u hu v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact hn i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

/-- In every sufficiently large odd prime field, selected nested intervals
have a common admissible translation with quantitative energy bounds. -/
theorem exists_admissible_interval_translates {ι : Type*}
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : ℕ) (hH : 4*H < p)
    (S : Finset ι) (length : ι → ℕ) (hlen : ∀ i ∈ S, length i ≤ H) :
    ∃ a : ZMod p,
      (∀ u ∈ intervalTranslate p a H, u ≠ 0) ∧
      (∀ u ∈ intervalTranslate p a H, ∀ v ∈ intervalTranslate p a H, u+v ≠ 0) ∧
      ∀ i ∈ S, (translatedEnergy (baseInterval p (length i)) a : ℝ) ≤
        8*S.card*(length i : ℝ)^2 := by
  obtain ⟨a,ha,hE⟩ := exists_simultaneous_small_translates
    (by simpa only [ZMod.ringChar_zmod_n] using hp)
    S (fun i ↦ baseInterval p (length i)) (forbiddenInterval p H) (by
      rw [ZMod.card]
      have hh := forbiddenInterval_card p H
      omega)
  obtain ⟨hzero,hopp⟩ := intervalTranslate_admissible p hp H a ha
  refine ⟨a,hzero,hopp,fun i hi ↦ ?_⟩
  have hc : (baseInterval p (length i)).card = length i := by
    simpa only [intervalTranslate,Finset.card_image_of_injective _ (add_right_injective a)] using
      intervalTranslate_card p a (show length i ≤ p by have := hlen i hi; omega)
  simpa only [hc] using hE i hi

end Erdos66CharacterTranslateSelection
