import Submission.Rigidity

/-! Cut obstructions for minimum cycle decompositions.
These are auxiliary lower bounds, not a disproof of Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184

lemma regular_two_isEdgeConnected {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (hr : G.IsRegularOfDegree 2) : G.IsEdgeConnected 2 := by
  have hcycles : G.IsCycles := by
    intro v _
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hr v
  apply SimpleGraph.isEdgeConnected_two.mpr
  refine ⟨hc.preconnected, ?_⟩
  intro e
  induction e using Sym2.ind with
  | h u v =>
    intro hb
    obtain ⟨huv, hnot⟩ := SimpleGraph.isBridge_iff.mp hb
    exact hnot (hcycles.reachable_deleteEdges huv)

lemma spanning_cycle_contains_two_cut_edge {V : Type*} [Fintype V]
    {G A : SimpleGraph V} (hA : A ≤ G) (hc : A.Connected)
    (hr : A.IsRegularOfDegree 2) (e f : Sym2 V)
    (hcut : ¬ (G.deleteEdges {e, f}).Preconnected) : e ∈ A.edgeSet := by
  by_contra he
  have htwo := regular_two_isEdgeConnected A hc hr
  have hle : A.deleteEdges {f} ≤ G.deleteEdges {e, f} := by
    intro u v huv
    obtain ⟨huv, hnot⟩ := SimpleGraph.deleteEdges_adj.mp huv
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hA huv, ?_⟩
    intro hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact he (hx ▸ (show s(u, v) ∈ A.edgeSet from huv))
    · exact hnot hx
  apply hcut
  intro u v
  exact (htwo u v (s := {f}) (by simp)).mono hle

lemma coe_connected_spanning_of_verts_univ {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) (hc : H.coe.Connected) (hverts : H.verts = Set.univ) :
    H.spanningCoe.Connected := by
  let φ : H.coe →g H.spanningCoe := {
    toFun := Subtype.val
    map_rel' := fun h => h }
  haveI : Nonempty V := hc.nonempty.map Subtype.val
  refine ⟨?_⟩
  intro u v
  have hu : u ∈ H.verts := hverts.symm ▸ Set.mem_univ u
  have hv : v ∈ H.verts := hverts.symm ▸ Set.mem_univ v
  exact (hc.preconnected ⟨u, hu⟩ ⟨v, hv⟩).map φ

lemma coe_regular_spanning_of_verts_univ {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) (hr : H.coe.IsRegularOfDegree 2) (hverts : H.verts = Set.univ) :
    H.spanningCoe.IsRegularOfDegree 2 := by
  intro v
  have hv : v ∈ H.verts := hverts.symm ▸ Set.mem_univ v
  have hh := hr ⟨v, hv⟩
  rw [Subgraph.coe_degree] at hh
  rw [Subgraph.degree_spanningCoe]
  simpa only [Subgraph.degree, ← Nat.card_eq_fintype_card] using hh

lemma cycle_decomposition_saturated_verts {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hdeg : ∀ v, G.degree v = 2 * D.card) :
    ∀ H ∈ D, H.verts = Set.univ := by
  intro H hH
  apply Set.eq_univ_of_forall
  intro v
  have hv := cycle_decomposition_vertex_count G D hcy hd v
  rw [hdeg v] at hv
  have heq : D.filter (fun K => v ∈ K.verts) = D := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    omega
  have hmem : H ∈ D.filter (fun K => v ∈ K.verts) := heq.symm ▸ hH
  exact (Finset.mem_filter.mp hmem).2

lemma spanning_cycle_decomposition_two_cut {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hspan : ∀ H ∈ D, H.verts = Set.univ)
    (e f : Sym2 V) (hcut : ¬ (G.deleteEdges {e, f}).Preconnected) : D.card ≤ 1 := by
  have hall : ∀ H ∈ D, e ∈ H.edgeSet := by
    intro H hH
    apply spanning_cycle_contains_two_cut_edge H.spanningCoe_le
      (coe_connected_spanning_of_verts_univ H (hcy H hH).1 (hspan H hH))
      (coe_regular_spanning_of_verts_univ H (hcy H hH).2 (hspan H hH)) e f hcut
  apply Finset.card_le_one.mpr
  intro H hH K hK
  by_contra hne
  exact Set.disjoint_left.mp (hd.1 hH hK hne) (hall H hH) (hall K hK)

lemma regular_four_two_cut_cycle_lower {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hr : G.IsRegularOfDegree 4)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (e f : Sym2 V) (hcut : ¬ (G.deleteEdges {e, f}).Preconnected) : 3 ≤ D.card := by
  have hlow := cycle_decomposition_degree_lower G D hcy hd (Classical.arbitrary V)
  rw [hr] at hlow
  by_contra hnot
  have hcard : D.card = 2 := by omega
  have hdeg : ∀ v, G.degree v = 2 * D.card := by
    intro v
    rw [hr, hcard]
  have hspan := cycle_decomposition_saturated_verts G D hcy hd hdeg
  have hh := spanning_cycle_decomposition_two_cut G D hcy hd hspan e f hcut
  omega

end Erdos184
