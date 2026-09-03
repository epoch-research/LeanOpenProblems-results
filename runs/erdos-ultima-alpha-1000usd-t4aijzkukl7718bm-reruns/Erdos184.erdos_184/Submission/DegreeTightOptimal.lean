import Submission.InvariantPartitions

/-!
The zero-slack case of optimal extendability. These results do not settle
Erdos 184: an optimum can be strictly larger than half the maximum degree.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace DegreeTightOptimal
open MinimalCounterexample

/-- In an all-optimal graph, attaining the degree lower bound at `v` forces
EVERY cycle, not just the pieces of the given decomposition, to contain `v`. -/
lemma every_cycle_mem_of_degree_tight {V : Type*} [Fintype V]
    {G : SimpleGraph V} (ho : AllCyclesOptimal G)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) (hv : G.degree v = 2 * D.card)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    v ∈ H.verts := by
  obtain ⟨E, hcE, hdE, hHE, hmE⟩ := ho H hH
  have hle := hmE D hc hd
  have hs := cycle_decomposition_vertex_count G E hcE hdE v
  have hsub : E.filter (fun K => v ∈ K.verts) ⊆ E := Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  have heq : E.filter (fun K => v ∈ K.verts) = E :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : H ∈ E.filter (fun K => v ∈ K.verts) := heq.symm ▸ hHE
  exact (Finset.mem_filter.mp hmem).2

/-- A common vertex of all cycles is a feedback vertex. -/
lemma delete_acyclic_of_every_cycle_mem {V : Type*} [Fintype V]
    {G : SimpleGraph V} (v : V)
    (hv : ∀ H : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) → v ∈ H.verts) :
    (G.deleteIncidenceSet v).IsAcyclic := by
  intro u p hp
  let A := G.deleteIncidenceSet v
  let H := promote (G.deleteIncidenceSet_le v) p.toSubgraph
  have hc := cycle_subgraph_regular A hp
  have hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    refine ⟨hc.1, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hc.2 w
  have hvH : v ∈ p.toSubgraph.verts := hv H hcH
  have hpos : 0 < p.toSubgraph.coe.degree ⟨v,hvH⟩ := by
    have h := hc.2 ⟨v,hvH⟩
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
    omega
  obtain ⟨w,hw⟩ := (p.toSubgraph.coe.degree_pos_iff_exists_adj ⟨v,hvH⟩).mp hpos
  have hA : A.Adj v w.val := p.toSubgraph.adj_sub hw
  exact (deleteIncidenceSet_adj.mp hA).2.1 rfl

lemma degree_le_delete_add_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) {v w : V} (hw : w ≠ v) :
    G.degree w ≤ (G.deleteIncidenceSet v).degree w + 1 := by
  have hs : G.neighborFinset w ⊆ insert v ((G.deleteIncidenceSet v).neighborFinset w) := by
    intro z hz
    by_cases hzv : z = v
    · simp [hzv]
    · apply Finset.mem_insert_of_mem
      exact ((G.deleteIncidenceSet v).mem_neighborFinset _ _).mpr
        (deleteIncidenceSet_adj.mpr ⟨(G.mem_neighborFinset _ _).mp hz, hw, hzv⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
  simpa only [card_neighborFinset_eq_degree] using hh

lemma exists_nonisolated_degree_one_of_acyclic {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ha : G.IsAcyclic) (hne : G ≠ ⊥) :
    ∃ v, G.degree v = 1 := by
  obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  let C := G.connectedComponentMk u
  have hu : u ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hu huv
  haveI : Nontrivial C := ⟨⟨⟨u,hu⟩, ⟨v,hv⟩,
    fun h => huv.ne (congrArg Subtype.val h)⟩⟩
  have ht : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph, ha.comap C.toSimpleGraph_hom Subtype.val_injective⟩
  obtain ⟨w,hw⟩ := ht.exists_vert_degree_one_of_nontrivial
  exact ⟨w.val, by simpa only [component_degree] using hw⟩

/-- A nonempty even simple graph with a feedback vertex has a degree-two
vertex. Isolated vertices in the ambient type cause no difficulty. -/
lemma exists_degree_two_of_feedback {V : Type*} [Fintype V]
    {G : SimpleGraph V} (he : ∀ w, Even (G.degree w)) (hne : G ≠ ⊥)
    (v : V) (ha : (G.deleteIncidenceSet v).IsAcyclic) :
    ∃ w, G.degree w = 2 := by
  let A := G.deleteIncidenceSet v
  have hA : A ≠ ⊥ := by
    intro hb
    obtain ⟨x,y,hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hex : ∃ w, w ≠ v ∧ 0 < G.degree w := by
      by_cases hxv : x = v
      · exact ⟨y, by simpa only [hxv] using hxy.symm.ne,
          (G.degree_pos_iff_exists_adj y).mpr ⟨x,hxy.symm⟩⟩
      · exact ⟨x,hxv,(G.degree_pos_iff_exists_adj x).mpr ⟨y,hxy⟩⟩
    obtain ⟨w,hw,hpos⟩ := hex
    have hle := degree_le_delete_add_one G hw
    have hbdeg : (G.deleteIncidenceSet v).degree w = 0 := by
      simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      change Nat.card (A.neighborSet w) = 0
      simp [hb]
    have hew := he w
    obtain ⟨k,hk⟩ := hew
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hle hbdeg hpos hk
    omega
  obtain ⟨w,hw⟩ := exists_nonisolated_degree_one_of_acyclic A ha hA
  have hwv : w ≠ v := by
    intro h
    subst w
    have hz : A.degree v = 0 := by
      apply (A.degree_eq_zero_iff_notMem_support v).mpr
      rintro ⟨z,hz⟩
      exact (deleteIncidenceSet_adj.mp hz).2.1 rfl
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hw hz
    omega
  have hle := degree_le_delete_add_one G hwv
  have hpos : 0 < G.degree w := by
    have hh : A.degree w ≤ G.degree w := SimpleGraph.degree_le_of_le
      (G.deleteIncidenceSet_le v)
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hw hh ⊢
    omega
  obtain ⟨k,hk⟩ := he w
  refine ⟨w,?_⟩
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hw hle hpos hk ⊢
  dsimp only [A] at hw
  omega

lemma all_optimal_degree_tight_has_degree_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} (he : ∀ w, Even (G.degree w)) (hne : G ≠ ⊥)
    (ho : AllCyclesOptimal G) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) (hv : G.degree v = 2 * D.card) :
    ∃ w, G.degree w = 2 :=
  exists_degree_two_of_feedback he hne v
    (delete_acyclic_of_every_cycle_mem v
      (every_cycle_mem_of_degree_tight ho D hc hd v hv))

/-- In the zero-slack case all decompositions have the same size. This is
not the false unrestricted implication from all-optimality to invariance. -/
lemma invariant_of_degree_tight {V : Type*} [Fintype V]
    {G : SimpleGraph V} (ho : AllCyclesOptimal G) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) (hv : G.degree v = 2 * D.card) :
    InvariantPartitions.HasInvariantCount G := by
  have hcard : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → 2 * E.card = G.degree v := by
    intro E hcE hdE
    have hs := cycle_decomposition_vertex_count G E hcE hdE v
    have hf : E.filter (fun H => v ∈ H.verts) = E := by
      apply Finset.filter_eq_self.mpr
      intro H hHE
      exact every_cycle_mem_of_degree_tight ho D hc hd v hv H (hcE H hHE)
    rwa [hf] at hs
  intro E F hcE hdE hcF hdF
  have he := hcard E hcE hdE
  have hf := hcard F hcF hdF
  omega

/-- If there is no degree-two vertex, every decomposition in an all-optimal
nonempty even graph lies strictly above each vertex-degree lower bound. -/
lemma strict_degree_slack {V : Type*} [Fintype V]
    {G : SimpleGraph V} (he : ∀ w, Even (G.degree w)) (hne : G ≠ ⊥)
    (ho : AllCyclesOptimal G) (hno : ∀ w, G.degree w ≠ 2)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) :
    G.degree v + 2 ≤ 2 * D.card := by
  have hs := cycle_decomposition_vertex_count G D hc hd v
  have hf := Finset.card_filter_le D (fun H => v ∈ H.verts)
  have hne' : G.degree v ≠ 2 * D.card := by
    intro h
    obtain ⟨w,hw⟩ := all_optimal_degree_tight_has_degree_two he hne ho D hc hd v h
    exact hno w hw
  obtain ⟨r,hr⟩ := he v
  omega

end DegreeTightOptimal
end Erdos184
