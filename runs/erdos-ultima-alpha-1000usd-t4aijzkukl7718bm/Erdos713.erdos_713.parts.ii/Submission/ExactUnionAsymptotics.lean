import FormalConjecturesUtil
import Submission.CompactStrictRootAudit


/-! Copies can be moved into a vertex set containing the support, provided
that the set is large enough to accommodate isolated forbidden vertices. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Support
universe u

open scoped Classical in
theorem contained_induce_of_support_subset {W : Type u} [Fintype W] {V : Type*} [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (S : Set V) (hS : G.support ⊆ S)
    (hcard : Fintype.card W ≤ Nat.card S) (h : H ⊑ G) : H ⊑ G.induce S := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ H : SimpleGraph W, Fintype.card W ≤ Nat.card S → H ⊑ G → H ⊑ G.induce S from
    hP _ W rfl H hcard h
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW H hc hHG
    by_cases hNoIso : ∀ a, ∃ b, H.Adj a b
    · obtain ⟨f⟩ := hHG
      have hfS (a : W) : f a ∈ S := by
        obtain ⟨b, hab⟩ := hNoIso a
        exact hS ⟨f b, f.toHom.map_adj hab⟩
      refine ⟨⟨⟨fun a => ⟨f a, hfS a⟩, ?_⟩, ?_⟩⟩
      · exact fun hab => f.toHom.map_adj hab
      · intro a b hab
        exact f.injective (congrArg Subtype.val hab)
    · push_neg at hNoIso
      obtain ⟨x, hx⟩ := hNoIso
      have hx0 : H.degree x = 0 := by
        apply (H.degree_eq_zero_iff_notMem_support x).mpr
        rintro ⟨b, hb⟩
        exact hx b hb
      have hsmall : Fintype.card ↥({x}ᶜ : Set W) < k :=
        (Fintype.card_subtype_lt (x := x) (by simp)).trans_eq hW
      have hc' : Fintype.card ↥({x}ᶜ : Set W) ≤ Nat.card S :=
        (Fintype.card_subtype_le _).trans hc
      have h' := ih _ hsmall _ rfl (H.induce {x}ᶜ) hc' ((show H.induce {x}ᶜ ⊑ H from
        ⟨Copy.induce H _⟩).trans hHG)
      obtain ⟨f⟩ := h'
      exact Erdos713Leaf.extend_isolated (G.induce S) H hx0 f (by
        simpa only [Nat.card_eq_fintype_card] using hc)

open scoped Classical in
theorem edges_le_of_free_induce {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (S : Set V) (hS : G.support ⊆ S)
    (hfree : H.Free (G.induce S)) :
    G.edgeFinset.card ≤ extremalNumber (Fintype.card V) H + Fintype.card W * Fintype.card V := by
  classical
  by_cases hc : Fintype.card W ≤ Nat.card S
  · have hfree' : H.Free G := fun h => hfree (contained_induce_of_support_subset H G S hS hc h)
    exact (card_edgeFinset_le_extremalNumber hfree').trans (Nat.le_add_right _ _)
  · have hcardS : Nat.card S ≤ Fintype.card V := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (· ∈ S)
    have hEdges : G.edgeFinset.card ≤ Fintype.card W * Fintype.card V := by
      rw [← card_edgeFinset_induce_of_support_subset hS]
      calc
        (G.induce S).edgeFinset.card ≤ (Fintype.card S).choose 2 := card_edgeFinset_le_card_choose_two
        _ ≤ Fintype.card S ^ 2 := Nat.choose_le_pow _ _
        _ ≤ Fintype.card W * Fintype.card V := by
          rw [Fintype.card_eq_nat_card, pow_two]
          exact Nat.mul_le_mul (by omega) hcardS
    exact hEdges.trans (Nat.le_add_left _ _)


end Erdos713Support

/- Disjoint unions differ from the maximum of their extremal functions by
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


end Erdos713SharpUnion

namespace Erdos713SharpUnion
open Finset Erdos713ComponentRates
universe u v

/-- A finite union of components contained in one forbidden graph differs
from that graph's extremal function by at most a linear term. No assumption
about isolated vertices or monotonicity in the host order is required. -/
theorem sum_asymptotic_iff_of_contained {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) (h₂ : H₂ ⊑ H₁)
    {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0) :
    (fun n : ℕ => (extremalNumber n (H₁ ⊕g H₂) : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) ↔
    (fun n : ℕ => (extremalNumber n H₁ : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) := by
  have hmax (n : ℕ) : max (extremalNumber n H₁ : ℝ) (extremalNumber n H₂ : ℝ) =
      (extremalNumber n H₁ : ℝ) := by
    apply max_eq_left
    exact_mod_cast h₂.extremalNumber_le (n := n)
  simpa only [hmax] using sum_asymptotic_iff_max H₁ H₂ ha hc

/-- Uniformly bounding the extremal numbers of the fibres bounds the entire
finite graph up to a linear error. The label type need not be finite. -/
theorem extremal_fibres_upper {W : Type u} [Fintype W] {I : Type v}
    (G : SimpleGraph W) (χ : W → I)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v) (n M : ℕ)
    (hF : ∀ i, extremalNumber n (G.induce {w | χ w = i}) ≤ M) :
    extremalNumber n G ≤ M + (Fintype.card W)^2 * n := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (χ : W → I),
      (∀ u v, G.Adj u v → χ u = χ v) →
      (∀ i, extremalNumber n (G.induce {w | χ w = i}) ≤ M) →
      extremalNumber n G ≤ M + k^2 * n from
    hP _ W rfl G χ hχ hF
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G χ hχ hF
    by_cases hne : Nonempty W
    swap
    · letI : IsEmpty W := not_nonempty_iff.mp hne
      rw [← Fintype.card_fin n, extremalNumber_le_iff]
      intro K _ hfree
      exact (hfree IsContained.of_isEmpty).elim
    let w : W := hne.some
    let i := χ w
    let S : Set W := {v | χ v = i}
    have hsmall : Fintype.card ↥(Sᶜ) < k :=
      (Fintype.card_subtype_lt (x := w) (by simp [S,i])).trans_eq hW
    have hχ' : ∀ u v : ↥(Sᶜ), (G.induce Sᶜ).Adj u v → χ u.val = χ v.val := by
      intro u v huv
      exact hχ _ _ huv
    have hF' : ∀ j, extremalNumber n
        ((G.induce Sᶜ).induce {v : ↥(Sᶜ) | χ v.val = j}) ≤ M := by
      intro j
      by_cases hj : j = i
      · subst j
        rw [← Fintype.card_fin n, extremalNumber_le_iff]
        intro K _ hfree
        exact (hfree (@IsContained.of_isEmpty _ _ _ _ ⟨fun v => v.val.prop v.prop⟩)).elim
      · exact (show (G.induce Sᶜ).induce {v : ↥(Sᶜ) | χ v.val = j} ⊑
            G.induce {v | χ v = j} from
          ⟨(fibreComplementIso G χ hj).toCopy⟩).extremalNumber_le.trans (hF j)
    have hSc := ih _ hsmall _ rfl (G.induce Sᶜ) (fun v => χ v.val) hχ' hF'
    have he : G.induce S ⊕g G.induce Sᶜ ≃g G := splitIso G S (by
      intro u v huv
      change χ u = i ↔ χ v = i
      rw [hχ u v huv])
    have hcard : Fintype.card S + Fintype.card ↥(Sᶜ) = k := by
      rw [Fintype.card_compl_set]
      have hle := Fintype.card_subtype_le (· ∈ S)
      simp only [Fintype.card_eq_nat_card] at hW hle ⊢
      change Nat.card S ≤ Nat.card W at hle
      omega
    have hmax : max (extremalNumber n (G.induce S)) (extremalNumber n (G.induce Sᶜ)) ≤
        M + (Fintype.card ↥(Sᶜ))^2 * n :=
      max_le ((hF i).trans (Nat.le_add_right _ _)) hSc
    have hsquare : (Fintype.card ↥(Sᶜ))^2 + k ≤ k^2 := by
      have h₁ := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hsmall)
      have h₂ := Nat.mul_le_mul_left (Fintype.card ↥(Sᶜ)) hsmall.le
      nlinarith
    rw [← extremalNumber_congr_right he]
    calc
      extremalNumber n (G.induce S ⊕g G.induce Sᶜ) ≤
          max (extremalNumber n (G.induce S)) (extremalNumber n (G.induce Sᶜ)) + k*n := by
        simpa only [hcard] using extremal_sum_max_bound (G.induce S) (G.induce Sᶜ) n
      _ ≤ M + ((Fintype.card ↥(Sᶜ))^2 + k)*n := by
        nlinarith [hmax]
      _ ≤ M + k^2*n := Nat.add_le_add_left (Nat.mul_le_mul_right n hsquare) M

theorem fibres_asymptotic_iff_of_contained {W : Type u} [Fintype W] {I : Type v}
    {U : Type*} (G : SimpleGraph W) (χ : W → I) (J : SimpleGraph U)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v) (hJ : J ⊑ G)
    (hF : ∀ i, G.induce {w | χ w = i} ⊑ J)
    {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0) :
    (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) ↔
    (fun n : ℕ => (extremalNumber n J : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) := by
  apply equivalent_iff_of_linear_gap ((Fintype.card W)^2)
    (fun _ => hJ.extremalNumber_le) _ ha hc
  intro n
  exact extremal_fibres_upper G χ hχ n (extremalNumber n J)
    (fun i => (hF i).extremalNumber_le)

theorem component_asymptotic_iff_of_contained {W : Type u} [Fintype W]
    (G : SimpleGraph W) (C : G.ConnectedComponent)
    (hC : ∀ D : G.ConnectedComponent, D.toSimpleGraph ⊑ C.toSimpleGraph)
    {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0) :
    (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) ↔
    (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) := by
  classical
  exact fibres_asymptotic_iff_of_contained G G.connectedComponentMk C.toSimpleGraph
    (fun _ _ huv => ConnectedComponent.connectedComponentMk_eq_of_adj huv)
    ⟨⟨C.toSimpleGraph_hom,Subtype.val_injective⟩⟩ hC ha hc

#print axioms extremal_fibres_upper
#print axioms component_asymptotic_iff_of_contained
end Erdos713SharpUnion

namespace Erdos713SharpUnion
open Erdos713Rate Erdos713ComponentRates
universe u v

/-- Removing one fibre leaves a subcritical extremal function when every
other fibre has an upper bound with exponent strictly below a. -/
theorem complement_subcritical_upper {W : Type u} [Fintype W] {I : Type v}
    (G : SimpleGraph W) (χ : W → I) (i : I) {a : ℝ} (ha : 1 < a)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v)
    (hF : ∀ j, j ≠ i → ∃ b : ℝ, 1 ≤ b ∧ b < a ∧
      (fun n : ℕ => (extremalNumber n (G.induce {w | χ w = j}) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^b)) :
    ∃ b : ℝ, 1 ≤ b ∧ b < a ∧
      (fun n : ℕ => (extremalNumber n (G.induce {w | χ w ≠ i}) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^b) := by
  classical
  apply subcritical_upper_of_fibres (G.induce {w | χ w ≠ i}) (fun w => χ w.val) ha
    (fun u v huv => hχ u.val v.val huv)
  intro j
  by_cases hj : j = i
  · subst j
    exact ⟨1,le_rfl,ha,(forest_rate _ (by
      intro v
      exact (v.val.prop v.prop).elim)).upper⟩
  · obtain ⟨b,hb,hba,hu⟩ := hF j hj
    exact ⟨b,hb,hba,(extremal_mono_bigO ⟨(fibreComplementIso G χ hj).toCopy⟩).trans hu⟩

/-- A unique non-subcritical fibre inherits the original exact asymptotic,
with its leading constant unchanged. -/
theorem fibre_asymptotic_of_other_subcritical {W : Type u} [Fintype W] {I : Type v}
    (G : SimpleGraph W) (χ : W → I) (i : I) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (hχ : ∀ u v, G.Adj u v → χ u = χ v)
    (hF : ∀ j, j ≠ i → ∃ b : ℝ, 1 ≤ b ∧ b < a ∧
      (fun n : ℕ => (extremalNumber n (G.induce {w | χ w = j}) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^b))
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) :
    (fun n : ℕ => (extremalNumber n (G.induce {w | χ w = i}) : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) := by
  classical
  let S : Set W := {w | χ w = i}
  obtain ⟨b,hb,hba,hu⟩ := complement_subcritical_upper G χ i ha hχ hF
  have he : G.induce Sᶜ ⊕g G.induce S ≃g G := Iso.sumComm.trans (splitIso G S (by
    intro u v huv
    change χ u = i ↔ χ v = i
    rw [hχ u v huv]))
  have heq (n : ℕ) : extremalNumber n (G.induce Sᶜ ⊕g G.induce S) = extremalNumber n G :=
    extremalNumber_congr_right he
  apply (right_asymptotic_iff_of_subdominant_left (G.induce Sᶜ) (G.induce S) ha hc
    (hu.trans_isLittleO (Erdos713Leaf.rpow_isLittleO_nat hba))).mp
  simpa only [heq] using h

theorem component_asymptotic_of_unique_rate {W : Type u} [Fintype W]
    (G : SimpleGraph W) (C : G.ConnectedComponent) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a))
    (hUnique : ∀ D : G.ConnectedComponent, HasRate D.toSimpleGraph a → D = C) :
    (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) := by
  classical
  have hG := rate_of_asymptotic ha.le hc h
  apply fibre_asymptotic_of_other_subcritical G G.connectedComponentMk C ha hc
    (fun _ _ huv => ConnectedComponent.connectedComponentMk_eq_of_adj huv) _ h
  intro D hDC
  have hu := (extremal_mono_bigO
    (show D.toSimpleGraph ⊑ G from ⟨⟨D.toSimpleGraph_hom,Subtype.val_injective⟩⟩)).trans hG.upper
  have hn : ¬ HasRate D.toSimpleGraph a := fun hd => hDC (hUnique D hd)
  have hl : ¬ ∀ b : ℝ, 1 ≤ b →
      ((fun n : ℕ => (extremalNumber n D.toSimpleGraph : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^b)) → a ≤ b := fun hl => hn ⟨ha.le,hu,hl⟩
  push_neg at hl
  obtain ⟨b,hb,hU,hba⟩ := hl
  exact ⟨b,hb,hba,hU⟩

/-- For any chosen component, failure of exact asymptotic transfer requires
another component attaining the same exponent. No individual limit follows
from the existence of several tied thresholds. -/
theorem component_asymptotic_or_competitor {W : Type u} [Fintype W]
    (G : SimpleGraph W) (C : G.ConnectedComponent) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) :
    ((fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) ∨
    ∃ D : G.ConnectedComponent, D ≠ C ∧ HasRate D.toSimpleGraph a := by
  classical
  by_cases hUnique : ∀ D : G.ConnectedComponent, HasRate D.toSimpleGraph a → D = C
  · exact Or.inl (component_asymptotic_of_unique_rate G C ha hc h hUnique)
  · push_neg at hUnique
    obtain ⟨D,hD,hDC⟩ := hUnique
    exact Or.inr ⟨D,hDC,hD⟩

theorem exact_component_or_two_rates {W : Type u} [Fintype W]
    (G : SimpleGraph W) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) :
    (∃ C : G.ConnectedComponent,
      (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
        (fun n : ℕ => c * (n : ℝ)^a)) ∨
    ∃ C D : G.ConnectedComponent, C ≠ D ∧ HasRate C.toSimpleGraph a ∧
      HasRate D.toSimpleGraph a := by
  obtain ⟨C,hC⟩ := exists_component_rate G ha (rate_of_asymptotic ha.le hc h)
  rcases component_asymptotic_or_competitor G C ha hc h with hExact | ⟨D,hDC,hD⟩
  · exact Or.inl ⟨C,hExact⟩
  · exact Or.inr ⟨C,D,hDC.symm,hC,hD⟩

#print axioms complement_subcritical_upper
#print axioms component_asymptotic_of_unique_rate
#print axioms component_asymptotic_or_competitor
#print axioms exact_component_or_two_rates
end Erdos713SharpUnion

namespace Erdos713SharpUnion
open Finset Erdos713Rate Erdos713ComponentRates
universe u

lemma asymptotic_of_small_gap {f g E : ℕ → ℕ} {a c : ℝ}
    (hlo : ∀ n, g n ≤ f n) (hhi : ∀ n, f n ≤ g n + E n)
    (hE : (fun n => (E n : ℝ)) =o[atTop] (fun n => c*(n : ℝ)^a))
    (h : (fun n => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^a)) :
    (fun n => (g n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^a) := by
  have hδO : (fun n => (f n : ℝ) - (g n : ℝ)) =O[atTop] (fun n => (E n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    have hlo' : (g n : ℝ) ≤ f n := by exact_mod_cast hlo n
    have hhi' : (f n : ℝ) ≤ (g n : ℝ) + (E n : ℝ) := by exact_mod_cast hhi n
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hlo'), Real.norm_natCast, one_mul]
    linarith
  apply (h.sub_isLittleO (hδO.trans_isLittleO hE)).congr_left
  filter_upwards with n
  simp only [Pi.sub_apply]
  ring

/-- It suffices for C to contain all components attaining the exponent.
The other components contribute only a smaller-order error. -/
theorem component_asymptotic_of_rate_domination {W : Type u} [Fintype W]
    (G : SimpleGraph W) (C : G.ConnectedComponent) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a))
    (hDom : ∀ D : G.ConnectedComponent, HasRate D.toSimpleGraph a →
      D.toSimpleGraph ⊑ C.toSimpleGraph) :
    (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a) := by
  classical
  let K := (univ : Finset G.ConnectedComponent).filter
    (fun D => ¬ D.toSimpleGraph ⊑ C.toSimpleGraph)
  have hG := rate_of_asymptotic ha.le hc h
  have hSmall (D : G.ConnectedComponent) (hD : D ∈ K) :
      (fun n : ℕ => (extremalNumber n D.toSimpleGraph : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ)^a) := by
    have hn : ¬ HasRate D.toSimpleGraph a := fun hR =>
      (mem_filter.mp hD).2 (hDom D hR)
    have hu := (extremal_mono_bigO
      (show D.toSimpleGraph ⊑ G from ⟨⟨D.toSimpleGraph_hom,Subtype.val_injective⟩⟩)).trans hG.upper
    have hl : ¬ ∀ b : ℝ, 1 ≤ b →
        ((fun n : ℕ => (extremalNumber n D.toSimpleGraph : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^b)) → a ≤ b := fun hl => hn ⟨ha.le,hu,hl⟩
    push_neg at hl
    obtain ⟨b,hb,hU,hba⟩ := hl
    exact hU.trans_isLittleO (Erdos713Leaf.rpow_isLittleO_nat hba)
  let E : ℕ → ℕ := fun n => (∑ D ∈ K, extremalNumber n D.toSimpleGraph) +
    (Fintype.card W)^2*n
  have hE : (fun n => (E n : ℝ)) =o[atTop] (fun n => c*(n : ℝ)^a) := by
    have hSum := IsLittleO.sum hSmall
    have hlin : (fun n : ℕ => (((Fintype.card W)^2*n : ℕ) : ℝ)) =o[atTop]
        (fun n => (n : ℝ)^a) := by
      simpa only [Nat.cast_mul,Real.rpow_one] using
        (Erdos713Leaf.rpow_isLittleO_nat ha).const_mul_left (((Fintype.card W)^2 : ℕ) : ℝ)
    apply IsLittleO.const_mul_right hc
    simpa only [E,Nat.cast_add,Nat.cast_sum] using hSum.add hlin
  have hhi (n : ℕ) : extremalNumber n G ≤ extremalNumber n C.toSimpleGraph + E n := by
    have hF : ∀ D : G.ConnectedComponent, extremalNumber n D.toSimpleGraph ≤
        extremalNumber n C.toSimpleGraph + ∑ D ∈ K, extremalNumber n D.toSimpleGraph := by
      intro D
      by_cases hDC : D.toSimpleGraph ⊑ C.toSimpleGraph
      · exact hDC.extremalNumber_le.trans (Nat.le_add_right _ _)
      · have hDK : D ∈ K := mem_filter.mpr ⟨mem_univ _,hDC⟩
        exact (single_le_sum (f := fun D => extremalNumber n D.toSimpleGraph)
          (fun _ _ => Nat.zero_le _) hDK).trans (Nat.le_add_left _ _)
    have hh := extremal_fibres_upper G G.connectedComponentMk
      (fun _ _ huv => ConnectedComponent.connectedComponentMk_eq_of_adj huv) n _ hF
    simpa only [E,Nat.add_assoc] using hh
  exact asymptotic_of_small_gap
    (fun _ => (show C.toSimpleGraph ⊑ G from
      ⟨⟨C.toSimpleGraph_hom,Subtype.val_injective⟩⟩).extremalNumber_le) hhi hE h

/-- Failure of exact transfer to C forces a threshold component not contained
in C. Merely duplicating components or adding smaller patterns is harmless. -/
theorem component_asymptotic_or_uncontained_rate {W : Type u} [Fintype W]
    (G : SimpleGraph W) (C : G.ConnectedComponent) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) :
    ((fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) ∨
    ∃ D : G.ConnectedComponent, ¬ D.toSimpleGraph ⊑ C.toSimpleGraph ∧
      HasRate D.toSimpleGraph a := by
  classical
  by_cases hDom : ∀ D : G.ConnectedComponent, HasRate D.toSimpleGraph a →
      D.toSimpleGraph ⊑ C.toSimpleGraph
  · exact Or.inl (component_asymptotic_of_rate_domination G C ha hc h hDom)
  · push_neg at hDom
    obtain ⟨D,hD,hDC⟩ := hDom
    exact Or.inr ⟨D,not_nonempty_iff.mpr hDC,hD⟩

private lemma greatest_of_total {I : Type*} (s : Finset I) (hs : s.Nonempty)
    (R : I → I → Prop) (hr : ∀ i, R i i) (ht : ∀ i j k, R i j → R j k → R i k)
    (hTotal : ∀ i ∈ s, ∀ j ∈ s, R i j ∨ R j i) :
    ∃ i ∈ s, ∀ j ∈ s, R j i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s has ih =>
    by_cases hs' : s.Nonempty
    · obtain ⟨b,hbs,hb⟩ := ih hs' (fun i hi j hj =>
        hTotal i (mem_insert_of_mem hi) j (mem_insert_of_mem hj))
      rcases hTotal b (mem_insert_of_mem hbs) a (mem_insert_self _ _) with hba | hab
      · refine ⟨a,mem_insert_self _ _,?_⟩
        intro j hj
        rcases mem_insert.mp hj with rfl | hjs
        · exact hr _
        · exact ht j b a (hb j hjs) hba
      · refine ⟨b,mem_insert_of_mem hbs,?_⟩
        intro j hj
        rcases mem_insert.mp hj with rfl | hjs
        · exact hab
        · exact hb j hjs
    · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs'
      subst s
      exact ⟨a,mem_insert_self _ _,by simpa using hr a⟩

/-- Either one connected component has the exact original asymptotic, or
two containment-incomparable components both attain the exponent. -/
theorem exact_component_or_incomparable_rates {W : Type u} [Fintype W]
    (G : SimpleGraph W) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ)^a)) :
    (∃ C : G.ConnectedComponent,
      (fun n : ℕ => (extremalNumber n C.toSimpleGraph : ℝ)) ~[atTop]
        (fun n : ℕ => c * (n : ℝ)^a)) ∨
    ∃ C D : G.ConnectedComponent, ¬ C.toSimpleGraph ⊑ D.toSimpleGraph ∧
      ¬ D.toSimpleGraph ⊑ C.toSimpleGraph ∧ HasRate C.toSimpleGraph a ∧
      HasRate D.toSimpleGraph a := by
  classical
  let S := (univ : Finset G.ConnectedComponent).filter (fun C => HasRate C.toSimpleGraph a)
  obtain ⟨C₀,hC₀⟩ := exists_component_rate G ha (rate_of_asymptotic ha.le hc h)
  have hS : S.Nonempty := ⟨C₀,mem_filter.mpr ⟨mem_univ _,hC₀⟩⟩
  by_cases hTotal : ∀ C ∈ S, ∀ D ∈ S,
      C.toSimpleGraph ⊑ D.toSimpleGraph ∨ D.toSimpleGraph ⊑ C.toSimpleGraph
  · obtain ⟨C,hCS,hC⟩ := greatest_of_total S hS
      (fun C D => C.toSimpleGraph ⊑ D.toSimpleGraph) (fun _ => .refl _)
      (fun _ _ _ h₁ h₂ => h₁.trans h₂) hTotal
    exact Or.inl ⟨C,component_asymptotic_of_rate_domination G C ha hc h
      (fun D hD => hC D (mem_filter.mpr ⟨mem_univ _,hD⟩))⟩
  · push_neg at hTotal
    obtain ⟨C,hCS,D,hDS,hCD,hDC⟩ := hTotal
    exact Or.inr ⟨C,D,not_nonempty_iff.mpr hCD,not_nonempty_iff.mpr hDC,
      (mem_filter.mp hCS).2,(mem_filter.mp hDS).2⟩

#print axioms component_asymptotic_of_rate_domination
#print axioms component_asymptotic_or_uncontained_rate
#print axioms exact_component_or_incomparable_rates
end Erdos713SharpUnion
