import Submission.BudgetedPackingExchange
import Submission.CountCritical

/-!
For count-critical graphs, a maximum-coverage packing with budget one below
the minimum leaves precisely a shortest cycle. This does not bound the
minimum count by the number of vertices.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.BudgetedCyclePacking
open CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Feasible.residual_ne_bot {k : ℕ} {D : Finset G.Subgraph}
    (hD : Feasible G k D) (hk : k < cycleNumber G) :
    G \ unionPieces G D ≠ ⊥ := by
  intro hR
  have hzero : (G \ unionPieces G D).edgeSet = ∅ := by simp [hR]
  rw [SimpleGraph.edgeSet_sdiff] at hzero
  have hcover : IsDecomposition G D := by
    refine ⟨hD.2.1, ?_⟩
    rw [← unionPieces_edgeSet]
    exact Set.Subset.antisymm (SimpleGraph.edgeSet_mono (unionPieces_le G D))
      (Set.diff_eq_empty.mp hzero)
  have hh := number_le G D hD.1 hcover
  have hb := hD.2.2
  omega

/-- Any budget below the minimum leaves an even nonempty graph and hence
at least girth(G) uncovered edges. -/
lemma Feasible.girth_le_residual {k : ℕ} {D : Finset G.Subgraph}
    (hD : Feasible G k D) (he : ∀ v, Even (G.degree v))
    (hk : k < cycleNumber G) :
    G.girth ≤ (G \ unionPieces G D).edgeSet.ncard := by
  have heR := even_residual_of_cycle_packing G he D hD.1 hD.2.1
  obtain ⟨u, p, hp⟩ := exists_cycle_of_even_nonempty (G \ unionPieces G D) (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using heR v) (hD.residual_ne_bot hk)
  have hl := girth_le_length (hp.mapLe (show G \ unionPieces G D ≤ G from sdiff_le))
  simp only [Walk.mapLe, Walk.length_map] at hl
  have hu := hp.isTrail.length_le_card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hu
  omega

lemma Feasible.weight_add_girth_le {k : ℕ} {D : Finset G.Subgraph}
    (hD : Feasible G k D) (he : ∀ v, Even (G.degree v))
    (hk : k < cycleNumber G) : weight D + G.girth ≤ G.edgeSet.ncard := by
  have hh := cycle_packing_edge_card_partition G D hD.2.1
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hh
  change weight D + (G \ unionPieces G D).edgeSet.ncard = G.edgeSet.ncard at hh
  have hg := hD.girth_le_residual he hk
  omega

/-- Criticality allows a shortest cycle to extend to a minimum partition.
Erasing it attains the largest possible covered-edge count at budget k. -/
lemma critical_exists_girth_complement {k : ℕ}
    (hG : IsCountCritical (k+1) G) :
    ∃ D : Finset G.Subgraph, Feasible G k D ∧
      weight D + G.girth = G.edgeSet.ncard := by
  have hne : G ≠ ⊥ := by
    intro hh
    have hn := hG.2.1
    rw [hh, number_bot] at hn
    omega
  have hnacyc : ¬G.IsAcyclic := by
    intro hh
    exact hne (even_acyclic_eq_bot G hG.1 hh)
  obtain ⟨u, p, hp, hg⟩ := exists_girth_eq_length.mpr hnacyc
  have hcH := cycle_subgraph_regular G hp
  obtain ⟨E, hcE, hdE, hmem, hcard⟩ := cycle_lift hG.1 p.toSubgraph hcH
  rw [hG.residual_number p.toSubgraph hcH] at hcard
  have hlow := number_le G E hcE hdE
  rw [hG.2.1] at hlow
  have hEq : E.card = k+1 := by omega
  have hfeas : Feasible G k (E.erase p.toSubgraph) := by
    refine ⟨fun H hH => hcE H (Finset.mem_of_mem_erase hH), ?_, ?_⟩
    · intro H hH K hK hne
      exact hdE.1 (Finset.mem_of_mem_erase hH) (Finset.mem_of_mem_erase hK) hne
    · rw [Finset.card_erase_of_mem hmem, hEq]
      omega
  have hlength : p.toSubgraph.edgeSet.ncard = G.girth := by
    have hh := trail_spanning_edge_card p hp.isTrail
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at hh
    exact hh.trans hg.symm
  have hsum : weight (E.erase p.toSubgraph) + p.toSubgraph.edgeSet.ncard = weight E :=
    Finset.sum_erase_add _ _ hmem
  have htotal := decomposition_edge_card G E hdE
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at htotal
  change weight E = G.edgeSet.ncard at htotal
  exact ⟨E.erase p.toSubgraph, hfeas, by omega⟩

lemma Optimal.critical_residual_card {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (hG : IsCountCritical (k+1) G) :
    (G \ unionPieces G D).edgeSet.ncard = G.girth := by
  obtain ⟨E, hE, hEweight⟩ := critical_exists_girth_complement hG
  have hmax := hm.2 E hE
  have hlow := hm.1.weight_add_girth_le hG.1 (by rw [hG.2.1]; omega)
  have hpart := cycle_packing_edge_card_partition G D hm.1.2.1
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hpart
  change weight D + (G \ unionPieces G D).edgeSet.ncard = G.edgeSet.ncard at hpart
  omega

/-- Exact residual characterization; no criticality of an arbitrary cycle
residual is inferred. The residual here is a specially optimized packing's
complement, at the specific budget k=minimum-1. -/
theorem Optimal.critical_residual_shortest_cycle {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (hG : IsCountCritical (k+1) G) :
    ∃ H : G.Subgraph,
      (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      H.spanningCoe = G \ unionPieces G D ∧ H.edgeSet.ncard = G.girth := by
  let R := G \ unionPieces G D
  have heR := even_residual_of_cycle_packing G hG.1 D hm.1.1 hm.1.2.1
  have hRne : R ≠ ⊥ := hm.1.residual_ne_bot (by rw [hG.2.1]; omega)
  obtain ⟨u, p, hp⟩ := exists_cycle_of_even_nonempty R (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using heR v) hRne
  have hcardR : R.edgeSet.ncard = G.girth := hm.critical_residual_card hG
  have hlower := girth_le_length (hp.mapLe (show R ≤ G from sdiff_le))
  simp only [Walk.mapLe, Walk.length_map] at hlower
  have hcardp : p.toSubgraph.edgeSet.ncard = p.length := by
    have hh := trail_spanning_edge_card p hp.isTrail
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hh
  have heq : p.toSubgraph.edgeSet = R.edgeSet := by
    apply Set.eq_of_subset_of_ncard_le p.toSubgraph.edgeSet_subset
    omega
  let H : G.Subgraph := promote (show R ≤ G from sdiff_le) p.toSubgraph
  have hc := cycle_subgraph_regular R hp
  refine ⟨H, ⟨hc.1, ?_⟩, ?_, ?_⟩
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hc.2 v
  · apply SimpleGraph.edgeSet_injective
    exact heq
  · change p.toSubgraph.edgeSet.ncard = G.girth
    rw [heq, hcardR]

end Erdos184.BudgetedCyclePacking
