import FormalConjecturesUtil
import Submission.Latest

/-! Disjoint unions differ from the maximum of their extremal functions by
at most a linear error, even when the forbidden graphs have isolated vertices. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713SharpUnion
open Finset Erdos713Union

open scoped Classical in
theorem free_sum_max_bound {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) (G : SimpleGraph V)
    (hfree : (H₁ ⊕g H₂).Free G) : G.edgeFinset.card ≤
      max (extremalNumber (Fintype.card V) H₁) (extremalNumber (Fintype.card V) H₂) +
        (Fintype.card A + Fintype.card B) * Fintype.card V := by
  classical
  by_cases hf : H₁.Free G
  · exact (card_edgeFinset_le_extremalNumber hf).trans
      ((le_max_left _ _).trans (Nat.le_add_right _ _))
  obtain ⟨f⟩ := not_not.mp hf
  let S : Finset V := univ.image f
  let T : Set V := (S : Set V)ᶜ
  let K := (G.induce T).spanningCoe
  have hS : S.card = Fintype.card A := by
    change ((univ : Finset A).image f.toHom).card = _
    rw [card_image_of_injective _ f.injective, card_univ]
  have hKfree : H₂.Free (G.induce T) := by
    rintro ⟨g⟩
    apply hfree
    apply sum_contained_of_disjoint_copies f ((Copy.induce G _).comp g)
    intro a b hab
    change f a = (g b).val at hab
    exact (g b).prop (hab ▸ mem_image_of_mem f (mem_univ a))
  have hSupp : K.support ⊆ T := by
    change ((G.induce T).map (Function.Embedding.subtype _)).support ⊆ T
    rw [support_map]
    rintro v ⟨w, _, rfl⟩
    exact w.prop
  have he := Erdos713Support.edges_le_of_free_induce H₂ K T hSupp (by
    simpa only [K, induce_spanningCoe] using hKfree)
  have hKeq : Nat.card K.edgeSet = Nat.card (G.induce T).edgeSet := by
    have hh := card_edgeFinset_map (Function.Embedding.subtype (· ∈ T)) (G.induce T)
    simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hh
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he
  rw [hKeq] at he
  have hb := edges_le_induce_compl_add G S
  rw [hS] at hb
  have hmax : extremalNumber (Fintype.card V) H₂ ≤
      max (extremalNumber (Fintype.card V) H₁) (extremalNumber (Fintype.card V) H₂) := le_max_right _ _
  rw [Nat.add_mul]
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hb hmax ⊢
  dsimp only [T] at he
  omega

open scoped Classical in
theorem extremal_sum_max_bound {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) (n : ℕ) :
    extremalNumber n (H₁ ⊕g H₂) ≤ max (extremalNumber n H₁) (extremalNumber n H₂) +
      (Fintype.card A + Fintype.card B) * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using free_sum_max_bound H₁ H₂ G hfree

theorem max_le_extremal_sum {A B : Type*} (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) (n : ℕ) :
    max (extremalNumber n H₁) (extremalNumber n H₂) ≤ extremalNumber n (H₁ ⊕g H₂) := by
  apply max_le
  · exact (show H₁ ⊑ H₁ ⊕g H₂ from ⟨Embedding.sumInl.toCopy⟩).extremalNumber_le
  · exact (show H₂ ⊑ H₁ ⊕g H₂ from ⟨Embedding.sumInr.toCopy⟩).extremalNumber_le

theorem equivalent_iff_of_linear_gap {f g : ℕ → ℕ} (C : ℕ)
    (hlo : ∀ n, g n ≤ f n) (hhi : ∀ n, f n ≤ g n + C * n)
    {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0) :
    IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => c * (n : ℝ) ^ a) ↔
      IsEquivalent atTop (fun n : ℕ => (g n : ℝ)) (fun n : ℕ => c * (n : ℝ) ^ a) := by
  have hδnonneg (n : ℕ) : 0 ≤ (f n : ℝ) - (g n : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hlo n
  have hδbound (n : ℕ) : (f n : ℝ) - (g n : ℝ) ≤ (C : ℝ) * (n : ℝ) := by
    have hh : (f n : ℝ) ≤ (g n : ℝ) + (C : ℝ) * (n : ℝ) := by exact_mod_cast hhi n
    linarith
  have hlin : (fun n : ℕ => (f n : ℝ) - (g n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
    apply IsBigO.of_bound (C : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (hδnonneg n), Real.norm_natCast]
    exact hδbound n
  have ho : (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ a) := by
    simpa only [Real.rpow_one] using Erdos713Leaf.rpow_isLittleO_nat ha
  have hδ := hlin.trans_isLittleO (ho.const_mul_right hc)
  constructor
  · intro h
    apply (h.sub_isLittleO hδ).congr_left
    filter_upwards with n
    simp only [Pi.sub_apply]
    ring
  · intro h
    apply (h.add_isLittleO hδ).congr_left
    filter_upwards with n
    simp only [Pi.add_apply]
    ring

theorem sum_asymptotic_iff_max {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n (H₁ ⊕g H₂) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) ↔
    IsEquivalent atTop (fun n : ℕ => max (extremalNumber n H₁ : ℝ) (extremalNumber n H₂ : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  simpa only [Nat.cast_max] using equivalent_iff_of_linear_gap
    (Fintype.card A + Fintype.card B) (max_le_extremal_sum H₁ H₂)
    (extremal_sum_max_bound H₁ H₂) ha hc

theorem right_asymptotic_iff_of_subdominant_left {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (hsmall : (fun n : ℕ => (extremalNumber n H₁ : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a)) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n (H₁ ⊕g H₂) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) ↔
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n H₂ : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  let C := Fintype.card A + Fintype.card B
  have hLo (n : ℕ) : extremalNumber n H₂ ≤ extremalNumber n (H₁ ⊕g H₂) :=
    (le_max_right _ _).trans (max_le_extremal_sum H₁ H₂ n)
  have hδnonneg (n : ℕ) : 0 ≤ (extremalNumber n (H₁ ⊕g H₂) : ℝ) - (extremalNumber n H₂ : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hLo n
  have hhi (n : ℕ) : extremalNumber n (H₁ ⊕g H₂) ≤
      extremalNumber n H₂ + (extremalNumber n H₁ + C * n) := by
    have hh := extremal_sum_max_bound H₁ H₂ n
    have hm : max (extremalNumber n H₁) (extremalNumber n H₂) ≤
        extremalNumber n H₁ + extremalNumber n H₂ := max_le (by omega) (by omega)
    dsimp only [C]
    omega
  have hδO : (fun n : ℕ => (extremalNumber n (H₁ ⊕g H₂) : ℝ) - (extremalNumber n H₂ : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n H₁ : ℝ) + ((C * n : ℕ) : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_of_nonneg (hδnonneg n), Real.norm_of_nonneg (by positivity), one_mul]
    have hh : (extremalNumber n (H₁ ⊕g H₂) : ℝ) ≤
        (extremalNumber n H₂ : ℝ) + ((extremalNumber n H₁ : ℝ) + ((C * n : ℕ) : ℝ)) := by
      exact_mod_cast hhi n
    linarith
  have hlin : (fun n : ℕ => ((C * n : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ a) := by
    simpa only [Nat.cast_mul, Real.rpow_one] using
      (Erdos713Leaf.rpow_isLittleO_nat ha).const_mul_left (C : ℝ)
  have hδ := hδO.trans_isLittleO ((hsmall.add hlin).const_mul_right hc)
  constructor
  · intro h
    apply (h.sub_isLittleO hδ).congr_left
    filter_upwards with n
    simp only [Pi.sub_apply]
    ring
  · intro h
    apply (h.add_isLittleO hδ).congr_left
    filter_upwards with n
    simp only [Pi.add_apply]
    ring

theorem right_asymptotic_of_irrational_of_left_rate {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) {r : ℚ} (hr : Erdos713Rate.HasRate H₁ (r : ℝ))
    {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0) (hIrr : a ∉ Set.range ((↑) : ℚ → ℝ))
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n (H₁ ⊕g H₂) : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n H₂ : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  have hle : (r : ℝ) ≤ a := hr.lower a ha.le
    ((Erdos713Rate.extremal_mono_bigO (show H₁ ⊑ H₁ ⊕g H₂ from ⟨Embedding.sumInl.toCopy⟩)).trans
      ((isBigO_const_mul_right_iff hc).mp h.isBigO))
  have hlt : (r : ℝ) < a := lt_of_le_of_ne hle (fun he => hIrr ⟨r, he⟩)
  exact (right_asymptotic_iff_of_subdominant_left H₁ H₂ ha hc
    (hr.upper.trans_isLittleO (Erdos713Leaf.rpow_isLittleO_nat hlt))).mp h

#print axioms right_asymptotic_of_irrational_of_left_rate
#print axioms free_sum_max_bound
#print axioms sum_asymptotic_iff_max

end Erdos713SharpUnion
