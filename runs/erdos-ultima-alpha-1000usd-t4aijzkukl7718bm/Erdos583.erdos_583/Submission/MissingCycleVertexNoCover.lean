import Submission.MissingCycleVertexObstruction

/-! The verified thirteen-vertex cycle/path obstruction has no two-path cover.
This is not a counterexample to the conjecture in Spec.lean. -/
namespace Erdos583MissingCycleVertexObstructionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583FinitePathSearchDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma degree_table (v : Fin 13) :
    G.degree v = if v=12 then 2 else if v=0 ∨ v=7 then 3 else 4 := by
  revert v
  decide

lemma two_subgraph_degree {H K : G.Subgraph}
    (hd : Disjoint H.edgeSet K.edgeSet) (hc : H.edgeSet ∪ K.edgeSet=G.edgeSet)
    (v : Fin 13) : (H.neighborSet v).ncard+(K.neighborSet v).ncard=G.degree v := by
  have he : H.neighborSet v ∪ K.neighborSet v=G.neighborSet v := by
    ext w
    change (s(v,w) ∈ H.edgeSet ∨ s(v,w) ∈ K.edgeSet) ↔ s(v,w) ∈ G.edgeSet
    rw [←Set.mem_union,hc]
  have hd' : Disjoint (H.neighborSet v) (K.neighborSet v) := by
    rw [Set.disjoint_left] at hd ⊢
    intro w hw hk
    exact hd (show s(v,w) ∈ H.edgeSet from hw) (show s(v,w) ∈ K.edgeSet from hk)
  rw [←Set.ncard_union_eq hd',he,neighborSet_ncard]

lemma path_spans_of_length {a b : Fin 13} (P : G.Walk a b) (hp : P.IsPath)
    (hl : P.length=12) (v : Fin 13) : v ∈ P.support := by
  have he : P.toSubgraph.verts=Set.univ := by
    apply (Set.eq_univ_iff_ncard _).mpr
    rw [InducedBuffer.path_vertex_ncard P hp,hl]
    simp only [Nat.card_fin]
  apply P.mem_verts_toSubgraph.mp
  rw [he]
  trivial

lemma no_two_path_cover : ¬TwoPathCover (G := G) G.edgeSet := by
  rintro ⟨a,b,c,d,P,Q,hP,hQ,hd,hcover⟩
  have hsum := Set.ncard_union_eq hd
  rw [hcover,QuotaSurgery.trail_edgeSet_ncard P hP.isTrail,
    QuotaSurgery.trail_edgeSet_ncard Q hQ.isTrail,edge_card] at hsum
  have hpbound := hP.length_lt
  have hqbound := hQ.length_lt
  simp only [Fintype.card_fin] at hpbound hqbound
  have hpL : P.length=12 := by omega
  have hqL : Q.length=12 := by omega
  have hpN : ¬P.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  have hqN : ¬Q.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  have hpPos := path_neighbor_ncard_pos hP hpN (path_spans_of_length P hP hpL 12)
  have hqPos := path_neighbor_ncard_pos hQ hqN (path_spans_of_length Q hQ hqL 12)
  have hdeg12 := two_subgraph_degree hd hcover 12
  rw [degree_table] at hdeg12
  simp only [ite_true] at hdeg12
  have hpOne : (P.toSubgraph.neighborSet 12).ncard=1 := by omega
  obtain ⟨b,R,hR,hPR⟩ := path_endpoint_of_neighbor_ncard_one ⟨a,b,P,hP,rfl⟩ hpOne
  have hRL : R.length=12 := by
    rw [←QuotaSurgery.trail_edgeSet_ncard R hR.isTrail,←hPR,
      QuotaSurgery.trail_edgeSet_ncard P hP.isTrail,hpL]
  have hRN : ¬R.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  have hne : b ≠ 12 := by
    intro hb
    subst b
    -- A nontrivial simple path has distinct endpoints.
    have he := hR.getVert_injOn (show 0 ≤ R.length by omega) (show R.length ≤ R.length by omega)
    have hn : (0 : ℕ)=R.length := he (by simp)
    omega
  have hRb : (R.toSubgraph.neighborSet b).ncard=1 := by
    rw [path_neighbor_ncard_formula hR hRN]
    simp
  have hQb := path_neighbor_ncard_le_two ⟨c,d,Q,hQ,rfl⟩ b
  have hdegb := two_subgraph_degree hd hcover b
  rw [hPR,hRb,degree_table] at hdegb
  have hb : b=0 ∨ b=7 := by
    by_contra hb
    simp only [hne,hb,ite_false] at hdegb
    omega
  rcases hb with rfl | rfl
  · exact no_path_of_search_false G next next_complete 12 12 0 search_zero ⟨R,hR,hRL⟩
  · exact no_path_of_search_false G next next_complete 12 12 7 search_seven ⟨R,hR,hRL⟩

lemma cycle_path_missing_vertex_not_absorbable :
    cycle.IsCycle ∧ path.IsPath ∧ (12 : Fin 13) ∉ path.support ∧
    Disjoint cycle.toSubgraph.edgeSet path.toSubgraph.edgeSet ∧
    ¬TwoPathCover (G := G) (cycle.toSubgraph.edgeSet ∪ path.toSubgraph.edgeSet) := by
  rw [edge_cover]
  exact ⟨cycle_isCycle,path_isPath,path_missing,edge_disjoint,no_two_path_cover⟩

end Erdos583MissingCycleVertexObstructionDevelopment
