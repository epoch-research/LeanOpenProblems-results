import Submission.TriangleArms

/-! A butterfly is absorbed at no path cost by vertex-disjoint paths meeting different petals. -/
namespace Erdos583ButterflyTwoPathsDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyPairsDevelopment Erdos583TriangleArmsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma butterfly_core_ncard {V : Type*} (f : Fin 5 → V) (hf : Function.Injective f) :
    (coreEdges baseSource baseTarget f).ncard=6 := by
  rw [base_coreEdges_eq]
  simp [Set.ncard_insert_of_notMem,hf.eq_iff]

lemma butterfly_two_disjoint_paths {V : Type*} [Fintype V] {G : SimpleGraph V} {a b c d : V}
    (f : Fin 5 → V) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (P : G.Walk a b) (Q : G.Walk c d) (hP : P.IsPath) (hQ : Q.IsPath)
    (hPQ : ∀ v ∈ P.support, v ∉ Q.support)
    (hrP : f 0 ∉ P.support) (hrQ : f 0 ∉ Q.support)
    (hxP : f 1 ∈ P.support) (hzQ : f 3 ∈ Q.support)
    (havoidP : ∀ e ∈ coreEdges baseSource baseTarget f, e ∉ P.toSubgraph.edgeSet)
    (havoidQ : ∀ e ∈ coreEdges baseSource baseTarget f, e ∉ Q.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (coreEdges baseSource baseTarget f ∪
      (P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet)) := by
  have h01 : G.Adj (f 0) (f 1) := ha 0
  have h12 : G.Adj (f 1) (f 2) := ha 1
  have h02 : G.Adj (f 0) (f 2) := (ha 2).symm
  have h03 : G.Adj (f 0) (f 3) := ha 3
  have h34 : G.Adj (f 3) (f 4) := ha 4
  have h04 : G.Adj (f 0) (f 4) := (ha 5).symm
  obtain ⟨a',b',X,Y,hX,hY,hXYe,hXYl,hXYs,h4X,h2Y⟩ :=
    triangle_arms_avoiding h01 h12 h02 P hP hrP hxP
      (show f 4 ≠ f 0 from fun hh ↦ (by decide : (4 : Fin 5) ≠ 0) (hf hh))
      (show f 4 ≠ f 1 from fun hh ↦ (by decide : (4 : Fin 5) ≠ 1) (hf hh))
      (show f 4 ≠ f 2 from fun hh ↦ (by decide : (4 : Fin 5) ≠ 2) (hf hh))
  obtain ⟨c',d',U,W,hU,hW,hUWe,hUWl,hUWs,h2U,h4W⟩ :=
    triangle_arms_avoiding h03 h34 h04 Q hQ hrQ hzQ
      (show f 2 ≠ f 0 from fun hh ↦ (by decide : (2 : Fin 5) ≠ 0) (hf hh))
      (show f 2 ≠ f 3 from fun hh ↦ (by decide : (2 : Fin 5) ≠ 3) (hf hh))
      (show f 2 ≠ f 4 from fun hh ↦ (by decide : (2 : Fin 5) ≠ 4) (hf hh))
  have h24 : f 2 ≠ f 4 := fun hh ↦ (by decide : (2 : Fin 5) ≠ 4) (hf hh)
  have hintXU : ∀ v ∈ X.support, v ∈ U.support → v=f 0 := by
    intro v hvX hvU
    rcases hXYs v (Or.inl hvX) with hv | hv | hv
    · exact hv
    · exact (h2U (hv ▸ hvU)).elim
    · rcases hUWs v (Or.inl hvU) with hh | hh | hh
      · exact hh
      · exact (h4X (hh ▸ hvX)).elim
      · exact (hPQ v hv hh).elim
  have hintYW : ∀ v ∈ Y.support, v ∈ W.support → v=f 0 := by
    intro v hvY hvW
    rcases hXYs v (Or.inr hvY) with hv | hv | hv
    · exact hv
    · subst v
      rcases hUWs (f 2) (Or.inr hvW) with hh | hh | hh
      · exact hh
      · exact (h24 hh).elim
      · exact (h2Y (fun h ↦ hPQ _ h hh) hvY).elim
    · rcases hUWs v (Or.inr hvW) with hh | hh | hh
      · exact hh
      · subst v
        exact (h4W (hPQ _ hv) hvW).elim
      · exact (hPQ _ hv hh).elim
  let A := X.reverse.append U
  let B := Y.reverse.append W
  have hA : A.IsPath := path_append_of_support_intersection hX.reverse hU (by
    intro v hvX hvU
    exact hintXU v (by simpa using hvX) hvU)
  have hB : B.IsPath := path_append_of_support_intersection hY.reverse hW (by
    intro v hvY hvW
    exact hintYW v (by simpa using hvY) hvW)
  have he : A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet=coreEdges baseSource baseTarget f ∪
      (P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet) := by
    have hsplit : A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet=
        (X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet) ∪ (U.toSubgraph.edgeSet ∪ W.toSubgraph.edgeSet) := by
      ext e
      simp only [A,B,Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_reverse,
        List.mem_append,List.mem_reverse,Set.mem_union]
      tauto
    rw [hsplit,hXYe,hUWe,base_coreEdges_eq]
    ext e
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := f 2) (b := f 0),Sym2.eq_swap (a := f 4) (b := f 0)]
    tauto
  have hdPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet :=
    edge_disjoint_of_one_common_vertex (r := f 0) P Q (fun v hp hq ↦ (hPQ v hp hq).elim)
  have hdC : Disjoint (coreEdges baseSource baseTarget f) (P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet) := by
    apply Set.disjoint_left.mpr
    rintro e he (hp|hq)
    · exact havoidP e he hp
    · exact havoidQ e he hq
  have hn : A.length+B.length=(coreEdges baseSource baseTarget f ∪
      (P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet)).ncard := by
    rw [Set.ncard_union_eq hdC,Set.ncard_union_eq hdPQ,butterfly_core_ncard f hf,
      trail_edgeSet_ncard P hP.isTrail,trail_edgeSet_ncard Q hQ.isTrail]
    simp only [A,B,Walk.length_append,Walk.length_reverse]
    omega
  exact ⟨a',c',b',d',A,B,hA,hB,disjoint_of_cover_length A B hA.isTrail hB.isTrail _ he hn,he⟩

end Erdos583ButterflyTwoPathsDevelopment
