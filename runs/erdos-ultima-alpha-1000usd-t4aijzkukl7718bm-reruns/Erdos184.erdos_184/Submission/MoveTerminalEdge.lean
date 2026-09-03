import Submission.FourOddTerminalSeparation

/-! Move an existing edge between sides, toggling exactly its endpoint parities. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteTerminalGluing
open TwoTerminalGluing TerminalRouting
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 300000

lemma odd_set_subset_support (A : SimpleGraph V) (S : Set V)
    (he : ∀ x, Even (A.degree x) ↔ x ∉ S) : S ⊆ A.support := by
  intro x hx
  by_contra hn
  have hz := (A.degree_eq_zero_iff_notMem_support x).mpr hn
  exact (he x).mp (by rw [hz]; decide) hx

lemma even_sup_edge_toggle {A : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (hn : ¬A.Adj a b) (S : Set V) (ha : a ∈ S) (hb : b ∈ S)
    (he : ∀ x, Even (A.degree x) ↔ x ∉ S) :
    ∀ x, Even ((A ⊔ edge a b).degree x) ↔ x ∉ S \ {a,b} := by
  have hd : Disjoint A.edgeSet (edge a b).edgeSet := by
    rw [edge_edgeSet_of_ne hab,Set.disjoint_singleton_right]
    exact hn
  intro x
  have hh := degree_sup_of_edge_disjoint A (edge a b) hd x
  have hm := degree_edge_eq hab x
  have hx := he x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hm hx ⊢
  rw [hh,hm]
  by_cases h : x = a ∨ x = b
  · have hxS : x ∈ S := h.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
    rw [if_pos h,Nat.even_add_one,hx]
    simp only [Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,hxS,h,true_and,not_true_eq_false,
      not_false_eq_true]
  · rw [if_neg h,Nat.add_zero,hx]
    simp only [Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,h,not_false_eq_true,and_true]

lemma even_sdiff_edge_toggle {A : SimpleGraph V} {a b : V}
    (hab : A.Adj a b) (S : Set V) (ha : a ∈ S) (hb : b ∈ S)
    (he : ∀ x, Even (A.degree x) ↔ x ∉ S) :
    ∀ x, Even ((A \ edge a b).degree x) ↔ x ∉ S \ {a,b} := by
  have hle : edge a b ≤ A := (edge_le_iff A).mpr (Or.inr hab)
  intro x
  have hh := degree_sdiff_of_le hle x
  have hm := degree_edge_eq hab.ne x
  have hx := he x
  have hl := degree_le_of_le hle (v := x)
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hm hx hl ⊢
  rw [hh,hm]
  rw [hm] at hl
  by_cases h : x = a ∨ x = b
  · have hxS : x ∈ S := h.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
    rw [if_pos h] at hl ⊢
    rw [Nat.even_sub hl,hx]
    simp only [Nat.not_even_one,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,
      hxS,h,true_and,not_true_eq_false,not_false_eq_true]
  · rw [if_neg h,Nat.sub_zero,hx]
    simp only [Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,h,not_false_eq_true,and_true]

/-- Moving an internal separator edge toggles its endpoints in the two odd
sets without enlarging either side's support. -/
lemma move_terminal_edge {G A B : SimpleGraph V} (S : Set V) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S)
    (hAG : A ≤ G) (hBG : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (heA : ∀ x, Even (A.degree x) ↔ x ∉ S)
    (heB : ∀ x, Even (B.degree x) ↔ x ∉ S) (hab : A.Adj a b) :
    ∃ X Y : SimpleGraph V, X ≤ G ∧ Y ≤ G ∧
      X.support ⊆ A.support ∧ Y.support ⊆ B.support ∧
      Disjoint X.edgeSet Y.edgeSet ∧ X.edgeSet ∪ Y.edgeSet = G.edgeSet ∧
      (∀ x, Even (X.degree x) ↔ x ∉ S \ {a,b}) ∧
      (∀ x, Even (Y.degree x) ↔ x ∉ S \ {a,b}) := by
  have hnB : ¬B.Adj a b := fun h => Set.disjoint_left.mp hd
    (show s(a,b) ∈ A.edgeSet from hab) (show s(a,b) ∈ B.edgeSet from h)
  have hEdgeA : (edge a b : SimpleGraph V).edgeSet ⊆ A.edgeSet := by
    rw [edge_edgeSet_of_ne hab.ne]
    exact Set.singleton_subset_iff.mpr hab
  refine ⟨A \ edge a b, B ⊔ edge a b,sdiff_le.trans hAG,
    sup_le hBG ((edge_le_iff G).mpr (Or.inr (hAG hab))),support_mono sdiff_le,?_,?_,?_,?_,?_⟩
  · rw [support_sup_eq,support_edge_eq hab.ne]
    refine Set.union_subset le_rfl ?_
    intro x hx
    apply odd_set_subset_support B S heB
    rcases hx with rfl | hx
    · exact ha
    · exact hx ▸ hb
  · rw [edgeSet_sdiff,edgeSet_sup]
    apply Set.disjoint_left.mpr
    intro e heA heB
    exact heB.elim (fun heB => Set.disjoint_left.mp hd heA.1 heB) heA.2
  · rw [edgeSet_sdiff,edgeSet_sup,← hu]
    ext e
    have he : e ∈ (edge a b : SimpleGraph V).edgeSet → e ∈ A.edgeSet := fun h => hEdgeA h
    simp only [Set.mem_union,Set.mem_diff]
    tauto
  · intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_sdiff_edge_toggle hab S ha hb heA x
  · intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_sup_edge_toggle hab.ne hnB S ha hb heB x

end Erdos184.FiniteTerminalGluing
