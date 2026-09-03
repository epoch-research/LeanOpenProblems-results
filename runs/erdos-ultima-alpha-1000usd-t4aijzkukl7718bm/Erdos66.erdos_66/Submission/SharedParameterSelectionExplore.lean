import Submission.IndexedCharacterEnergyExplore
import Submission.CharacterTranslateSelectionExplore
import Submission.SharedParameterRootExplore

/-! Simultaneous control of the two character sequences and their product.
The conclusion concerns finite, parameter-weighted root counts only. -/
namespace Erdos66SharedParameterSelection
open Erdos66IndexedCharacterEnergy Erdos66CharacterTranslateSelection
  Erdos66SharedParameterKernel Erdos66SharedParameterRoot Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 1500000

lemma interval_label_mem {p : ℕ} (a : ZMod p) (h i : ℕ) (hi : i<h) :
    a+(i : ZMod p)∈intervalTranslate p a h :=
  Finset.mem_image.mpr ⟨(i : ZMod p),Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩,rfl⟩

noncomputable def badPairs (p q h : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Finset (ZMod p × ZMod q) :=
  ((forbiddenInterval p h) ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ (forbiddenInterval q h))

lemma badPairs_card (p q h : ℕ) [Fact p.Prime] [Fact q.Prime] :
    (badPairs p q h).card ≤ 2*h*q+p*(2*h) := by
  have hh := Finset.card_union_le
    ((forbiddenInterval p h) ×ˢ (Finset.univ : Finset (ZMod q)))
    ((Finset.univ : Finset (ZMod p)) ×ˢ (forbiddenInterval q h))
  simp only [Finset.card_product,Finset.card_univ,ZMod.card] at hh
  exact hh.trans (Nat.add_le_add (Nat.mul_le_mul_right q (forbiddenInterval_card p h))
    (Nat.mul_le_mul_left p (forbiddenInterval_card q h)))

noncomputable def totalEnergy (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (ab : ZMod p × ZMod q) : ℤ :=
  indexedEnergy h (fun _ ↦ 1) ab.1 + indexedEnergy h (fun _ ↦ 1) ab.2 +
    indexedEnergy h (fun i ↦ quadraticChar (ZMod q) (ab.2+i)) ab.1

lemma totalEnergy_nonneg (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (ab : ZMod p × ZMod q) : 0 ≤ totalEnergy p q h ab :=
  add_nonneg (add_nonneg (indexedEnergy_nonneg _ _ _) (indexedEnergy_nonneg _ _ _))
    (indexedEnergy_nonneg _ _ _)

lemma totalEnergy_average (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hhp : h ≤ p) (hhq : h ≤ q) :
    (∑ ab : ZMod p × ZMod q, totalEnergy p q h ab) ≤
      12*(p : ℤ)*q*(h : ℤ)^2 := by
  have h₁ := average_indexed_energy hp h hhp (fun _ ↦ 1) (by intro i hi; norm_num)
  have h₂ := average_indexed_energy hq h hhq (fun _ ↦ 1) (by intro i hi; norm_num)
  have h₃ (b : ZMod q) := average_indexed_energy hp h hhp
    (fun i ↦ quadraticChar (ZMod q) (b+i)) (fun i hi ↦ quadraticChar_abs_le_one _)
  have hsum₁ : (∑ a : ZMod p, ∑ _b : ZMod q, indexedEnergy h (fun _ ↦ 1) a) ≤
      4*(p : ℤ)*q*(h : ℤ)^2 := by
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg q)
    nlinarith
  have hsum₂ : (∑ _a : ZMod p, ∑ b : ZMod q, indexedEnergy h (fun _ ↦ 1) b) ≤
      4*(p : ℤ)*q*(h : ℤ)^2 := by
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg p)
    nlinarith
  have hsum₃ : (∑ a : ZMod p, ∑ b : ZMod q,
      indexedEnergy h (fun i ↦ quadraticChar (ZMod q) (b+i)) a) ≤
      4*(p : ℤ)*q*(h : ℤ)^2 := by
    rw [Finset.sum_comm]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ h₃ b)
    simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul] at hh
    nlinarith
  simp only [totalEnergy,Fintype.sum_prod_type,Finset.sum_add_distrib]
  linarith

/-- One pair of translates has all three energies at most 24 h², and neither
parameter interval contains zero or an opposite pair. -/
theorem exists_shared_low_energy (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hh : 0 < h) (hp : 8*h < p) (hq : 8*h < q) :
    ∃ a : ZMod p, ∃ b : ZMod q,
      (∀ i<h, a+(i : ZMod p) ≠ 0) ∧
      (∀ i<h, b+(i : ZMod q) ≠ 0) ∧
      (∀ i<h, ∀ j<h, (a+(i : ZMod p))+(a+(j : ZMod p)) ≠ 0) ∧
      (∀ i<h, ∀ j<h, (b+(i : ZMod q))+(b+(j : ZMod q)) ≠ 0) ∧
      labelEnergy h (fun i ↦ (quadraticChar (ZMod p) (a+i) : ℝ)) ≤ 24*(h : ℝ)^2 ∧
      labelEnergy h (fun i ↦ (quadraticChar (ZMod q) (b+i) : ℝ)) ≤ 24*(h : ℝ)^2 ∧
      labelEnergy h (fun i ↦ (quadraticChar (ZMod p) (a+i) : ℝ)*
        (quadraticChar (ZMod q) (b+i) : ℝ)) ≤ 24*(h : ℝ)^2 := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hcard : 2*(badPairs p q h).card < Fintype.card (ZMod p × ZMod q) := by
    simp only [Fintype.card_prod,ZMod.card]
    have hc := badPairs_card p q h
    have h₁ := Nat.mul_lt_mul_of_pos_right hp hq0
    have h₂ := Nat.mul_lt_mul_of_pos_right hq hp0
    nlinarith
  have hav : (∑ ab : ZMod p × ZMod q, (totalEnergy p q h ab : ℝ)) ≤
      (Fintype.card (ZMod p × ZMod q) : ℝ)*(12*(h : ℝ)^2) := by
    have hh' := totalEnergy_average p q h (by omega) (by omega) (by omega) (by omega)
    have hr : (∑ ab : ZMod p × ZMod q, (totalEnergy p q h ab : ℝ)) ≤
        12*(p : ℝ)*q*(h : ℝ)^2 := by exact_mod_cast hh'
    simp only [Fintype.card_prod,ZMod.card,Nat.cast_mul]
    nlinarith
  obtain ⟨⟨a,b⟩,hab,he⟩ := exists_small_outside (badPairs p q h)
    (fun ab ↦ (totalEnergy p q h ab : ℝ)) (12*(h : ℝ)^2) hcard
    (fun ab ↦ by dsimp only; exact_mod_cast totalEnergy_nonneg p q h ab) hav
  have ha : a∉forbiddenInterval p h := by
    intro ha
    apply hab
    exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨ha,Finset.mem_univ _⟩)
  have hb : b∉forbiddenInterval q h := by
    intro hb
    apply hab
    exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_univ _,hb⟩)
  obtain ⟨ha0,haa⟩ := intervalTranslate_admissible p (by omega) h a ha
  obtain ⟨hb0,hbb⟩ := intervalTranslate_admissible q (by omega) h b hb
  refine ⟨a,b,(fun i hi ↦ ha0 _ (interval_label_mem a h i hi)),
    (fun i hi ↦ hb0 _ (interval_label_mem b h i hi)),
    (fun i hi j hj ↦ haa _ (interval_label_mem a h i hi) _ (interval_label_mem a h j hj)),
    (fun i hi j hj ↦ hbb _ (interval_label_mem b h i hi) _ (interval_label_mem b h j hj)),?_⟩
  have h₁ : (0 : ℝ) ≤ indexedEnergy h (fun _ ↦ 1) a := by exact_mod_cast indexedEnergy_nonneg h (fun _ ↦ 1) a
  have h₂ : (0 : ℝ) ≤ indexedEnergy h (fun _ ↦ 1) b := by exact_mod_cast indexedEnergy_nonneg h (fun _ ↦ 1) b
  have h₃ : (0 : ℝ) ≤ indexedEnergy h (fun i ↦ quadraticChar (ZMod q) (b+i)) a := by
    exact_mod_cast indexedEnergy_nonneg h (fun i ↦ quadraticChar (ZMod q) (b+i)) a
  simp only [totalEnergy,Int.cast_add] at he
  have he₁ : (indexedEnergy h (fun _ ↦ 1) a : ℝ) ≤ 24*(h : ℝ)^2 := by linarith
  have he₂ : (indexedEnergy h (fun _ ↦ 1) b : ℝ) ≤ 24*(h : ℝ)^2 := by linarith
  have he₃ : (indexedEnergy h (fun i ↦ quadraticChar (ZMod q) (b+i)) a : ℝ) ≤ 24*(h : ℝ)^2 := by linarith
  constructor
  · simpa only [indexedEnergy_eq_labelEnergy,Int.cast_one,one_mul] using he₁
  constructor
  · simpa only [indexedEnergy_eq_labelEnergy,Int.cast_one,one_mul] using he₂
  · simpa only [indexedEnergy_eq_labelEnergy,mul_comm] using he₃

/-- The shared two-field weighted root count has error O(h^(3/2)), uniformly
in both targets, while the main term remains h². -/
theorem exists_shared_root_flat (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hh : 0 < h) (hp : 8*h < p) (hq : 8*h < q) :
    ∃ a : ZMod p, ∃ b : ZMod q, ∀ t s : ZMod p, ∀ t' s' : ZMod q,
      (sharedRootCount h (fun i ↦ a+i) (fun i ↦ b+i) t s t' s'-(h : ℝ)^2)^2 ≤
        432*(h : ℝ)^3 := by
  obtain ⟨a,b,ha,hb,haa,hbb,hf,hg,hfg⟩ := exists_shared_low_energy p q h hh hp hq
  refine ⟨a,b,fun t s t' s' ↦ ?_⟩
  have he := sharedRootCount_error_sq h a b
    (by simpa only [ZMod.ringChar_zmod_n] using (show p ≠ 2 by omega))
    (by simpa only [ZMod.ringChar_zmod_n] using (show q ≠ 2 by omega))
    ha hb haa hbb 24 hf hg hfg t s t' s'
  norm_num at he ⊢
  exact he

end Erdos66SharedParameterSelection
