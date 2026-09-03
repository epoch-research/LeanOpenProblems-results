import Submission.PairedIntegrated

/-! A same-count separation criterion: switch two paths at their only common
vertex, provided the marked edges lie on opposite sides of that vertex.
The uniqueness-of-intersection hypothesis cannot simply be dropped. -/
namespace Erdos583SingleIntersectionSeparationDevelopment
open SimpleGraph Erdos583Work Erdos583Work.SharedExpansion
open Erdos583Work.SeparateTwoEdges Erdos583Work.RootedTailSystem
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V}

lemma separated_of_distinct_owners {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {A B : G.Subgraph}
    (hA : A ∈ D) (hB : B ∈ D) (hAB : A ≠ B)
    {e f : Sym2 V} (he : e ∈ A.edgeSet) (hf : f ∈ B.edgeSet) :
    Separated D ![e,f] := by
  apply (two_separated_iff D e f).mpr
  intro K hK ⟨heK,hfK⟩
  by_cases hKA : K=A
  · subst K
    exact Set.disjoint_left.mp (hD.2.1 hA hB hAB) hfK hf
  · exact Set.disjoint_left.mp (hD.2.1 hK hA hKA) heK he

lemma replace_pair_separated {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {H K A B : G.Subgraph}
    (hH : H ∈ D) (hK : K ∈ D) (hHK : H ≠ K)
    (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (hd : Disjoint A.edgeSet B.edgeSet)
    (hc : A.edgeSet ∪ B.edgeSet=H.edgeSet ∪ K.edgeSet)
    {e f : Sym2 V} (he : e ∈ A.edgeSet) (hf : f ∈ B.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card ∧
      Separated E ![e,f] := by
  classical
  let E := insert A (insert B ((D.erase H).erase K))
  have hE : GoodDecomposition G E := hD.replace_two hH hK hA hB hd hc
  have hAB : A ≠ B := by
    intro h
    exact Set.disjoint_left.mp hd he (h ▸ he)
  refine ⟨E,hE,?_,separated_of_distinct_owners hE
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hAB he hf⟩
  have h1 := Finset.card_erase_add_one hH
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hHK.symm,hK⟩)
  have h3 := Finset.card_insert_le B ((D.erase H).erase K)
  have h4 := Finset.card_insert_le A (insert B ((D.erase H).erase K))
  dsimp only [E]
  omega

lemma swap_single_intersection {a b c d w : V}
    (P : G.Walk a w) (R : G.Walk w b) (Q : G.Walk c w) (S : G.Walk w d)
    (hPR : (P.append R).IsPath) (hQS : (Q.append S).IsPath)
    (hdis : Disjoint (P.append R).toSubgraph.edgeSet (Q.append S).toSubgraph.edgeSet)
    (hint : ∀ x, x ∈ (P.append R).support → x ∈ (Q.append S).support → x=w) :
    (P.append S).IsPath ∧ (Q.append R).IsPath ∧
      Disjoint (P.append S).toSubgraph.edgeSet (Q.append R).toSubgraph.edgeSet ∧
      (P.append S).toSubgraph.edgeSet ∪ (Q.append R).toSubgraph.edgeSet =
        (P.append R).toSubgraph.edgeSet ∪ (Q.append S).toSubgraph.edgeSet := by
  have hPS : (P.append S).IsPath := path_append_of_support_intersection
    hPR.of_append_left hQS.of_append_right (by
      intro x hx hy
      exact hint x ((Walk.mem_support_append_iff _ _).mpr (Or.inl hx))
        ((Walk.mem_support_append_iff _ _).mpr (Or.inr hy)))
  have hQR : (Q.append R).IsPath := path_append_of_support_intersection
    hQS.of_append_left hPR.of_append_right (by
      intro x hx hy
      exact hint x ((Walk.mem_support_append_iff _ _).mpr (Or.inr hy))
        ((Walk.mem_support_append_iff _ _).mpr (Or.inl hx)))
  have hdPR := append_trail_disjoint hPR.isTrail
  have hdQS := append_trail_disjoint hQS.isTrail
  simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hdis ⊢
  refine ⟨hPS,hQR,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    rcases he with he|he <;> rcases hf with hf|hf
    · exact Set.disjoint_left.mp hdis (Or.inl he) (Or.inl hf)
    · exact Set.disjoint_left.mp hdPR he hf
    · exact Set.disjoint_left.mp hdQS hf he
    · exact Set.disjoint_left.mp hdis (Or.inr hf) (Or.inr he)
  · ext e
    simp only [Set.mem_union]
    tauto

lemma separate_at_single_intersection {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {a b c d w : V}
    (P : G.Walk a w) (R : G.Walk w b) (Q : G.Walk c w) (S : G.Walk w d)
    (hPR : (P.append R).IsPath) (hQS : (Q.append S).IsPath)
    (hP : (P.append R).toSubgraph ∈ D) (hQ : (Q.append S).toSubgraph ∈ D)
    (hne : (P.append R).toSubgraph ≠ (Q.append S).toSubgraph)
    (hint : ∀ x, x ∈ (P.append R).support → x ∈ (Q.append S).support → x=w)
    {e f : Sym2 V} (he : e ∈ P.edges) (hf : f ∈ R.edges) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card ∧
      Separated E ![e,f] := by
  obtain ⟨hPS,hQR,hd,hcov⟩ := swap_single_intersection P R Q S hPR hQS
    (hD.2.1 hP hQ hne) hint
  apply replace_pair_separated hD hP hQ hne
    ⟨a,d,P.append S,hPS,rfl⟩ ⟨c,b,Q.append R,hQR,rfl⟩ hd hcov
  · rw [Walk.mem_edges_toSubgraph,Walk.edges_append]
    exact List.mem_append.mpr (Or.inl he)
  · rw [Walk.mem_edges_toSubgraph,Walk.edges_append]
    exact List.mem_append.mpr (Or.inr hf)

lemma forced_owner_no_single_intersection {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {e f : Sym2 V}
    (hforced : ∀ E : Finset G.Subgraph, GoodDecomposition G E → E.card ≤ D.card →
      ∃ K ∈ E, e ∈ K.edgeSet ∧ f ∈ K.edgeSet)
    {a b c d w : V}
    (P : G.Walk a w) (R : G.Walk w b) (Q : G.Walk c w) (S : G.Walk w d)
    (hPR : (P.append R).IsPath) (hQS : (Q.append S).IsPath)
    (hP : (P.append R).toSubgraph ∈ D) (hQ : (Q.append S).toSubgraph ∈ D)
    (hne : (P.append R).toSubgraph ≠ (Q.append S).toSubgraph)
    (he : e ∈ P.edges) (hf : f ∈ R.edges) :
    ∃ x, x ∈ (P.append R).support ∧ x ∈ (Q.append S).support ∧ x ≠ w := by
  by_contra hno
  have hint (x) (hx : x ∈ (P.append R).support) (hy : x ∈ (Q.append S).support) : x=w := by
    by_contra hxw
    exact hno ⟨x,hx,hy,hxw⟩
  obtain ⟨E,hE,hEc,hs⟩ := separate_at_single_intersection hD P R Q S hPR hQS hP hQ hne hint he hf
  obtain ⟨K,hK,heK,hfK⟩ := hforced E hE hEc
  exact (two_separated_iff E e f).mp hs K hK ⟨heK,hfK⟩

end Erdos583SingleIntersectionSeparationDevelopment
