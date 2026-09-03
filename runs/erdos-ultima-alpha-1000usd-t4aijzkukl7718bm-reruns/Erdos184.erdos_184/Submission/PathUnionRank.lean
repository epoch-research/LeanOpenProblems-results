import Submission.ThreeTerminalGluing

/-!
A rank bound for the union of two paths with common endpoints. Unlike a
fixed-size terminal lemma, the cost is the actual number of common vertices.
These auxiliary bounds do not settle the cycle decomposition conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.PathUnionRank
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 200000

lemma closed_trail_toSubgraph_even {u : V} (p : G.Walk u u) (hp : p.IsTrail) :
    ∀ x, Even (p.toSubgraph.coe.degree x) := by
  have ht : p.mapToSubgraph.IsTrail := by
    have hh := hp.edges_nodup
    rw [← p.map_mapToSubgraph_hom, Walk.edges_map] at hh
    exact ⟨hh.of_map⟩
  have he : p.mapToSubgraph.IsEulerian := by
    apply ht.isEulerian_of_forall_mem
    intro e he
    have hm' : Sym2.map p.toSubgraph.hom e ∈ p.toSubgraph.edgeSet := by
      simpa only [← p.toSubgraph.image_coe_edgeSet_coe] using
        (Set.mem_image_of_mem (Sym2.map p.toSubgraph.hom) he)
    have hmem := p.mem_edges_toSubgraph.mp hm'
    have hmapped := congrArg Walk.edges p.map_mapToSubgraph_hom
    rw [← hmapped, Walk.edges_map] at hmem
    obtain ⟨d,hd,hde⟩ := List.mem_map.mp hmem
    have hde' : d = e := Sym2.map.injective p.toSubgraph.hom_injective hde
    exact hde' ▸ hd
  intro x
  have hh := (he.even_degree_iff (x := x)).mpr (by simp)
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hh

/-- A closed trail decomposes at its usual edge-minus-vertex rank cost. -/
lemma closed_trail_packing {u : V} (p : G.Walk u u) (hp : p.IsTrail) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ D, H.edgeSet) = p.toSubgraph.edgeSet ∧
      D.card + p.toSubgraph.verts.ncard ≤ p.length + 1 := by
  obtain ⟨E,hc,hd⟩ := even_cycle_decomposition p.toSubgraph.coe (by
    intro x
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using closed_trail_toSubgraph_even p hp x)
  have hb := connected_cycle_decomposition_rank_bound p.toSubgraph.coe
    p.toSubgraph_connected E (by
      intro A hA
      refine ⟨(hc A hA).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hc A hA).2 x) hd
  obtain ⟨D,hcD,hdD,hcov,hcard⟩ := lift_cycle_decomposition p.toSubgraph E (by
    intro A hA
    refine ⟨(hc A hA).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hc A hA).2 x) hd
  have heq := trail_spanning_edge_card p hp
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at heq
  change p.toSubgraph.edgeSet.ncard = p.length at heq
  rw [coe_edgeFinset_card,heq] at hb
  simp only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hb
  exact ⟨D,hcD,hdD,hcov,by omega⟩

omit [Fintype V] in
lemma path_verts_card {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.toSubgraph.verts.ncard = p.length+1 := by
  have hs : p.toSubgraph.verts = (p.support.toFinset : Set V) := by
    ext x
    simp only [Walk.mem_verts_toSubgraph,Finset.mem_coe,List.mem_toFinset]
  rw [hs,Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]

/-- Edge-disjoint paths a--b and b--a decompose into at most one fewer cycles
than their number of shared vertices. No order assumption on the shared
vertices along either path is made. -/
lemma paths_to_packing {a b : V} (p : G.Walk a b) (q : G.Walk b a)
    (hp : p.IsPath) (hq : q.IsPath) (hedge : p.edges.Disjoint q.edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ e, e ∈ ⋃ H ∈ D, H.edgeSet ↔ e ∈ p.edges ∨ e ∈ q.edges) ∧
      D.card + 1 ≤ (p.toSubgraph.verts ∩ q.toSubgraph.verts).ncard := by
  have ht : (p.append q).IsTrail := by
    rw [Walk.isTrail_def,Walk.edges_append,List.nodup_append']
    exact ⟨hp.isTrail.edges_nodup,hq.isTrail.edges_nodup,hedge⟩
  obtain ⟨D,hc,hd,hcov,hcard⟩ := closed_trail_packing (p.append q) ht
  have hs := Set.ncard_union_add_ncard_inter p.toSubgraph.verts q.toSubgraph.verts
  rw [path_verts_card p hp,path_verts_card q hq] at hs
  simp only [Walk.toSubgraph_append,Subgraph.verts_sup,Walk.length_append] at hcard
  refine ⟨D,hc,hd,?_,by omega⟩
  intro e
  rw [hcov,Walk.mem_edges_toSubgraph,Walk.edges_append,List.mem_append]

lemma paths_to_packing_of_inter_subset {a b : V}
    (p : G.Walk a b) (q : G.Walk b a)
    (hp : p.IsPath) (hq : q.IsPath) (hedge : p.edges.Disjoint q.edges)
    (S : Set V) (hi : p.toSubgraph.verts ∩ q.toSubgraph.verts ⊆ S) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ e, e ∈ ⋃ H ∈ D, H.edgeSet ↔ e ∈ p.edges ∨ e ∈ q.edges) ∧
      D.card + 1 ≤ S.ncard := by
  obtain ⟨D,hc,hd,hcov,hcard⟩ := paths_to_packing p q hp hq hedge
  exact ⟨D,hc,hd,hcov,hcard.trans (Set.ncard_le_ncard hi)⟩

end Erdos184.PathUnionRank
