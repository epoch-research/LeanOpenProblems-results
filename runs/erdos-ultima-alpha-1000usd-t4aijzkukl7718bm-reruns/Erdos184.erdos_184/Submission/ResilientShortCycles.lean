import Submission.PackingEdgeDeletionPaths

/-! Short simple cycles through remaining edges after a controlled packing.
No claim of a linear-cost full packing follows from these local extensions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit ExpansionPaths
universe u
variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
set_option maxHeartbeats 1000000

/-- Closing a short avoiding-edge path produces a genuine simple cycle. -/
lemma IsVertexMinimal.short_cycle_after_packing (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hP : P.card+256 ≤ C) {u v : V} (huv : (G \ unionPieces G P).Adj u v) :
    ∃ p : (G \ unionPieces G P).Walk u u,
      p.IsCycle ∧ s(u,v) ∈ p.edges ∧
      p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1)+3 := by
  let R := G \ unionPieces G P
  let F : Set (Sym2 V) := {s(u,v)}
  have hF : F.ncard = 1 := Set.ncard_singleton _
  obtain ⟨q,hq,hlen⟩ := hG.short_path_after_packing_edges (by omega) P hc hd F
    (by omega) (by omega) v u
  have hn : ¬q.Nil := Walk.not_nil_of_ne huv.ne.symm
  have hp0 := Walk.not_nil_iff_lt_length.mp hn
  have hp1 : q.length ≠ 1 := by
    intro h
    have ha := q.adj_of_length_eq_one h
    have hh := (SimpleGraph.deleteEdges_adj.mp ha).2
    exact hh (by simp [F,Sym2.eq_swap])
  have hp2 : 2 ≤ q.length := by omega
  let a := q.mapLe (R.deleteEdges_le F)
  have ha : a.IsPath := hq.mapLe _
  have hal : a.length = q.length := by simp [a]
  let p := a.cons huv
  have hp : p.IsCycle := path_close_isCycle a ha (by omega) huv
  refine ⟨p,hp,?_,?_⟩
  · simp only [p,Walk.edges_cons,List.mem_cons,true_or]
  · simp only [p,Walk.length_cons]
    omega

lemma IsVertexMinimal.short_cycle_through_edge (hG : IsVertexMinimal C G)
    (hC : 256 ≤ C) {u v : V} (huv : G.Adj u v) :
    ∃ p : G.Walk u u, p.IsCycle ∧ s(u,v) ∈ p.edges ∧
      p.length ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1)+3 := by
  have h := hG.short_cycle_after_packing ∅ (by simp) (by simp) (by simpa using hC)
    (u := u) (v := v)
  have he : unionPieces G ∅ = ⊥ := by ext a b; simp [unionPieces]
  obtain ⟨p,hp,heP,hlen⟩ := h (by rw [he,sdiff_bot]; exact huv)
  exact ⟨p.mapLe sdiff_le,hp.mapLe _,by simpa using heP,by simpa using hlen⟩

/-- In the lexicographically minimal class, this short cycle can be retained
in a full optimum. Different specified edges may require different optima. -/
lemma IsLexMinimal.short_piece_through_edge (hG : IsLexMinimal C G)
    (hC : 256 ≤ C) {u v : V} (huv : G.Adj u v) :
    ∃ (D : Finset G.Subgraph) (H : G.Subgraph),
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ s(u,v) ∈ H.edgeSet ∧
      H.edgeSet.ncard ≤ 24*scale (Fintype.card V)*(Nat.log 2 (Fintype.card V)+1)+3 ∧
      D.card = budget C (Fintype.card V)+1 := by
  obtain ⟨p,hp,he,hlen⟩ := hG.1.short_cycle_through_edge hC huv
  have hc := cycle_subgraph_regular G hp
  obtain ⟨D,hD,hd,hPD,hcard⟩ := hG.extend_cycle p.toSubgraph hc
  have hlen' : p.toSubgraph.edgeSet.ncard = p.length := by
    have h := trail_spanning_edge_card p hp.isTrail
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using h
  exact ⟨D,p.toSubgraph,hD,hd,hPD,by simpa using he,by omega,hcard⟩

end Erdos184.LogDeficitSeparator
