import Submission.RankBlocks

/-!\nA local transition condition in connected rank-critical graphs.  Prescribing
one pair of edges at one vertex is possible in an optimum.  This does not
assert that multiple pairs can be prescribed simultaneously.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace CriticalNeighborPairs

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Close a path avoiding `v` with the two prescribed edges at `v`. -/
lemma cycle_of_avoiding_path {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath) (hv : v ∉ p.support) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      H.Adj v a ∧ H.Adj v b := by
  let q := p.concat hvb.symm
  have hq : q.IsPath := by
    rw [Walk.isPath_def, Walk.support_concat]
    exact hp.support_nodup.concat hv
  have he : s(v,a) ∉ q.edges := by
    simp only [q, Walk.edges_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton]
    rintro (he | he)
    · exact hv (p.fst_mem_support_of_mem_edges he)
    · rcases Sym2.eq_iff.mp he with h | h
      · exact hva.ne h.2.symm
      · exact hab h.2
  let c := Walk.cons hva q
  have hc : c.IsCycle := (Walk.cons_isCycle_iff _ _).mpr ⟨hq, he⟩
  refine ⟨c.toSubgraph, cycle_subgraph_regular G hc, ?_, ?_⟩
  · apply Walk.adj_toSubgraph_iff_mem_edges.mpr
    simp [c]
  · apply Walk.adj_toSubgraph_iff_mem_edges.mpr
    simp [c, q, Walk.edges_concat, Sym2.eq_swap]

/-- Connectivity after deletion of `v` permits any distinct neighbor pair. -/
lemma cycle_of_connected_without {v a b : V}
    (hc : (G.induce {x | x ≠ v}).Connected)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      H.Adj v a ∧ H.Adj v b := by
  let f : (G.induce {x | x ≠ v}) →g G :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  obtain ⟨p, hp⟩ := (hc.preconnected ⟨a, hva.ne.symm⟩ ⟨b, hvb.ne.symm⟩).exists_isPath
  apply cycle_of_avoiding_path hva hvb hab (p.map f)
    (Walk.map_isPath_of_injective Subtype.val_injective hp)
  simp only [Walk.support_map, List.mem_map, not_exists, not_and]
  intro x _ hx
  exact x.property hx


/-- Any two distinct incident edges can be paired within a cycle of some
minimum decomposition.  The optimum is the rank-critical value. -/
lemma critical_optimal_neighbor_pair {C : ℕ} (hG : RankCritical.IsCritical C G)
    (hc : G.Connected) {v a b : V}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) :
    ∃ (D : Finset G.Subgraph) (H : G.Subgraph),
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ H.Adj v a ∧ H.Adj v b ∧
      D.card = C * RankCritical.graphRank G + 1 := by
  obtain ⟨H, hH, ha, hb⟩ := cycle_of_connected_without
    (RankBlocks.critical_induce_without_connected hG hc v) hva hvb hab
  obtain ⟨D, hD, hd, hmem, hn⟩ := hG.extend_cycle H hH
  exact ⟨D, H, hD, hd, hmem, ha, hb, hn⟩

end CriticalNeighborPairs
end Erdos184
