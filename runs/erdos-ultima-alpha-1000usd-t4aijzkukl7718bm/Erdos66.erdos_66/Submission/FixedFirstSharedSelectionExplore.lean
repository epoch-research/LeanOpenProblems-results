import Submission.SharedParameterSelectionExplore

/-! Select a second character translate without changing a prescribed first
sequence. This is finite-label compatibility, not integer-prefix compatibility. -/
namespace Erdos66FixedFirstSharedSelection
open Erdos66IndexedCharacterEnergy Erdos66CharacterTranslateSelection
  Erdos66SharedParameterSelection Erdos66SharedParameterKernel
  Erdos66SharedParameterRoot Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 1500000

/-- A fixed bounded signed sequence and the constant sequence can both be
controlled by one admissible translate in the new field. -/
theorem exists_extension_low_energy (q h : ℕ) [Fact q.Prime]
    (hh : 0<h) (hq : 4*h<q) (f : ℕ → ℤ) (hf : ∀ i<h, |f i|≤1) :
    ∃ b : ZMod q,
      (∀ i<h, b+(i : ZMod q) ≠ 0) ∧
      (∀ i<h, ∀ j<h, (b+(i : ZMod q))+(b+(j : ZMod q)) ≠ 0) ∧
      labelEnergy h (fun i ↦ (quadraticChar (ZMod q) (b+i) : ℝ)) ≤ 16*(h : ℝ)^2 ∧
      labelEnergy h (fun i ↦ (f i : ℝ)*(quadraticChar (ZMod q) (b+i) : ℝ)) ≤ 16*(h : ℝ)^2 := by
  have hq2 : q ≠ 2 := by omega
  have hcard : 2*(forbiddenInterval q h).card < Fintype.card (ZMod q) := by
    rw [ZMod.card]
    have := forbiddenInterval_card q h
    omega
  let E : ZMod q → ℝ := fun b ↦
    (indexedEnergy h (fun _ ↦ 1) b : ℝ)+(indexedEnergy h f b : ℝ)
  have hnon : ∀ b, 0≤E b := by
    intro b
    exact add_nonneg (by exact_mod_cast indexedEnergy_nonneg _ _ _)
      (by exact_mod_cast indexedEnergy_nonneg _ _ _)
  have hav : (∑ b, E b) ≤ (Fintype.card (ZMod q) : ℝ)*(8*(h : ℝ)^2) := by
    have h₁ := average_indexed_energy hq2 h (by omega) (fun _ ↦ 1) (by intro i hi; norm_num)
    have h₂ := average_indexed_energy hq2 h (by omega) f hf
    have h₁' : (∑ b : ZMod q, (indexedEnergy h (fun _ ↦ 1) b : ℝ)) ≤
        4*(q : ℝ)*(h : ℝ)^2 := by exact_mod_cast h₁
    have h₂' : (∑ b : ZMod q, (indexedEnergy h f b : ℝ)) ≤
        4*(q : ℝ)*(h : ℝ)^2 := by exact_mod_cast h₂
    simp only [E,Finset.sum_add_distrib,ZMod.card]
    linarith
  obtain ⟨b,hb,he⟩ := exists_small_outside (forbiddenInterval q h) E (8*(h : ℝ)^2)
    hcard hnon hav
  obtain ⟨hb0,hbb⟩ := intervalTranslate_admissible q hq2 h b hb
  refine ⟨b,(fun i hi ↦ hb0 _ (interval_label_mem b h i hi)),
    (fun i hi j hj ↦ hbb _ (interval_label_mem b h i hi) _ (interval_label_mem b h j hj)),?_⟩
  have hn₁ : (0 : ℝ) ≤ indexedEnergy h (fun _ ↦ 1) b :=
    by exact_mod_cast indexedEnergy_nonneg _ _ _
  have hn₂ : (0 : ℝ) ≤ indexedEnergy h f b := by exact_mod_cast indexedEnergy_nonneg _ _ _
  have he₁ : (indexedEnergy h (fun _ ↦ 1) b : ℝ) ≤ 16*(h : ℝ)^2 := by dsimp [E] at he; linarith
  have he₂ : (indexedEnergy h f b : ℝ) ≤ 16*(h : ℝ)^2 := by dsimp [E] at he; linarith
  constructor
  · simpa only [indexedEnergy_eq_labelEnergy,Int.cast_one,one_mul] using he₁
  · simpa only [indexedEnergy_eq_labelEnergy] using he₂

/-- The old translate is fixed. Only the second translate is selected. -/
theorem exists_fixed_first_root_flat (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hh : 0<h) (hp : p ≠ 2) (hq : 4*h<q) (a : ZMod p)
    (ha : ∀ i<h, a+(i : ZMod p) ≠ 0)
    (haa : ∀ i<h, ∀ j<h, (a+(i : ZMod p))+(a+(j : ZMod p)) ≠ 0)
    (C : ℝ) (hC : 16≤C)
    (hE : labelEnergy h (fun i ↦ (quadraticChar (ZMod p) (a+i) : ℝ)) ≤ C*(h : ℝ)^2) :
    ∃ b : ZMod q,
      (∀ i<h, b+(i : ZMod q) ≠ 0) ∧
      (∀ i<h, ∀ j<h, (b+(i : ZMod q))+(b+(j : ZMod q)) ≠ 0) ∧
      ∀ t s : ZMod p, ∀ t' s' : ZMod q,
        (sharedRootCount h (fun i ↦ a+i) (fun i ↦ b+i) t s t' s'-(h : ℝ)^2)^2 ≤
          18*C*(h : ℝ)^3 := by
  obtain ⟨b,hb,hbb,hg,hfg⟩ := exists_extension_low_energy q h hh hq
    (fun i ↦ quadraticChar (ZMod p) (a+i)) (fun i hi ↦ quadraticChar_abs_le_one _)
  refine ⟨b,hb,hbb,fun t s t' s' ↦ ?_⟩
  have hbound : 16*(h : ℝ)^2 ≤ C*(h : ℝ)^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  exact sharedRootCount_error_sq h a b
    (by simpa only [ZMod.ringChar_zmod_n] using hp)
    (by simpa only [ZMod.ringChar_zmod_n] using (show q ≠ 2 by omega))
    ha hb haa hbb C hE (hg.trans hbound) (hfg.trans hbound) t s t' s'

end Erdos66FixedFirstSharedSelection
