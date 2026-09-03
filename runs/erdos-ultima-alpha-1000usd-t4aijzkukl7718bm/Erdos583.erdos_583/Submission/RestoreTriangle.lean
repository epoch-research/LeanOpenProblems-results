import Submission.OneMemberReplacement

/-! Adding an edge-disjoint triangle at the support of a path partition. -/
namespace Erdos583RestoreTriangleDevelopment
open SimpleGraph Erdos583Work
open Erdos583OneMemberReplacementDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma restore_triangle_at_support {V : Type*} [Fintype V] {F G : SimpleGraph V}
    (hFG : F ≤ G) {r x y : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ {s(r,x),s(x,y),s(r,y)})
    (htouch : ∃ v ∈ F.support, v ∈ ({r,x,y} : Set V))
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  obtain ⟨v,⟨w,hvw⟩,hvC⟩ := htouch
  have he : s(v,w) ∈ F.edgeSet := hvw
  rw [←hD.2.2] at he
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp he
  obtain ⟨a,b,P,hP,hKe⟩ := hD.1 K hKD
  let Q := P.mapLe hFG
  have hQ : Q.IsPath := hP.mapLe hFG
  have hQe : Q.toSubgraph.edgeSet=K.edgeSet := by
    rw [hKe]; simp only [Q,Walk.edgeSet_toSubgraph,Walk.edges_mapLe_eq_edges]
  have hvQ : v ∈ Q.support := by
    simp only [Q,Walk.support_mapLe_eq_support]
    exact P.fst_mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp (hKe ▸ heK))
  obtain ⟨u,v',s,t,A,B,hA,hB,hAB,hABe⟩ := TriangleAbsorption.triangle_path_absorption
    hrx hxy hry Q hQ ⟨v,hvQ,hvC⟩
    (fun e he hh ↦ Set.disjoint_left.mp hdis he (K.edgeSet_subset (hQe ▸ hh)))
  rw [hQe] at hABe
  have hrest : Disjoint (A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet) (F.edgeSet \ K.edgeSet) := by
    rw [hABe]
    apply Set.disjoint_left.mpr
    rintro e (he|he) hh
    · exact hh.2 he
    · exact Set.disjoint_left.mp hdis he hh.1
  have hcov : G.edgeSet=((F.edgeSet \ K.edgeSet) ∪ A.toSubgraph.edgeSet) ∪ B.toSubgraph.edgeSet := by
    rw [Set.union_assoc,hABe,hcover]
    ext e
    simp only [Set.mem_union,Set.mem_diff]
    constructor
    · rintro (he|he)
      · by_cases hk : e ∈ K.edgeSet
        · exact Or.inr (Or.inl hk)
        · exact Or.inl ⟨he,hk⟩
      · exact Or.inr (Or.inr he)
    · rintro (he|he|he)
      · exact Or.inl he.1
      · exact Or.inl (K.edgeSet_subset he)
      · exact Or.inr he
  exact replace_one_by_two hFG D hD K hKD A.toSubgraph B.toSubgraph
    ⟨_,_,A,hA,rfl⟩ ⟨_,_,B,hB,rfl⟩ hAB (disjoint_sup_left.mp hrest).1
    (disjoint_sup_left.mp hrest).2 hcov

end Erdos583RestoreTriangleDevelopment
