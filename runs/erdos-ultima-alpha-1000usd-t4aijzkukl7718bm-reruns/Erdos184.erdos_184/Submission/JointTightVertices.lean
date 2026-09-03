import Submission.NonCliqueSmoothing

/-!
Combining global vertex minimality with edge-criticality rules out adjacent
vertices at the critical degree threshold. This is a necessary condition only.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace JointTightVertices
open GlobalVertexMinimal MinimalCounterexample NonCliqueSmoothing

lemma four_cycle_chord {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v a u b : V} (hva : G.Adj v a) (hau : G.Adj a u)
    (hub : G.Adj u b) (hbv : G.Adj b v) (hvu : v ≠ u) (hab : a ≠ b) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      v ∈ H.verts ∧ u ∈ H.verts ∧ ¬H.Adj v u := by
  let p : G.Walk v b := .cons hva (.cons hau (.cons hub .nil))
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    simp [p, hva.ne, hau.ne, hub.ne, hbv.ne.symm, hvu, hab]
  let c := p.cons hbv
  have hc : c.IsCycle := path_close_isCycle p hp (by simp [p]) hbv
  refine ⟨c.toSubgraph, cycle_subgraph_regular G hc, ?_, ?_, ?_⟩
  · simp [c, p]
  · simp [c, p]
  · intro h
    have he : s(v,u) ∈ c.edges := c.mem_edges_toSubgraph.mp h
    simp [c, p, hva.ne, hub.ne, hau.ne.symm, hbv.ne.symm, hvu, hvu.symm] at he

universe u
lemma tight_vertices_independent {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hglob : IsVertexMinimal C G)
    (hcrit : IsCritical C G) (hC : 0 < C) :
    G.IsIndepSet {v | G.degree v = 2 * (C+1)} := by
  intro v hv u hu _ huv
  have hcl := low_degree_neighbors_clique hglob v hv.le
  have hmem : u ∈ G.neighborFinset v := by simpa using huv
  have hc : 1 < ((G.neighborFinset v).erase u).card := by
    rw [Finset.card_erase_of_mem hmem, card_neighborFinset_eq_degree, hv]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hc
  have hau := (Finset.mem_erase.mp ha).1
  have hbu := (Finset.mem_erase.mp hb).1
  have hva : G.Adj v a := by simpa using (Finset.mem_erase.mp ha).2
  have hvb : G.Adj v b := by simpa using (Finset.mem_erase.mp hb).2
  obtain ⟨H,hH,hvH,huH,hn⟩ := four_cycle_chord hva
    (hcl hva huv hau) (hcl huv hvb hbu.symm) hvb.symm huv.ne hab
  exact hn (hcrit.tight_edge_not_chord huv hv hu H hH hvH huH)

end JointTightVertices
end Erdos184
