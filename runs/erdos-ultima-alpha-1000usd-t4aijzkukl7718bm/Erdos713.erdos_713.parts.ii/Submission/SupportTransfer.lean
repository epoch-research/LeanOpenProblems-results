import FormalConjecturesUtil
import Submission.Verified

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

#print axioms contained_induce_of_support_subset
#print axioms edges_le_of_free_induce

end Erdos713Support
