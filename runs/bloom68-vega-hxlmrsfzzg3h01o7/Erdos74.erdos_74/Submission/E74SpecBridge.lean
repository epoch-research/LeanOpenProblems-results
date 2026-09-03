import Submission.E74Basic
import Submission.Spec

/-!
# From the numerical specification to hereditary small cuts

This module uses only the four distance definitions in `Submission.Spec`.
All minima, bounds, and Boolean cuts needed for the bridge are proved here.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Finite vertex support gives finite ambient edge support, even when `V` is infinite. -/
theorem edgeSet_finite_of_verts_finite (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.Finite := by
  classical
  letI := hA.fintype
  rw [← A.image_coe_edgeSet_coe]
  exact (Set.toFinite A.coe.edgeSet).image _

/-- Deleting every edge always gives a bipartite graph. -/
theorem isBipartite_delete_all_edges (A : G.Subgraph) :
    IsBipartite (A.deleteEdges A.edgeSet).coe := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ ↦ (0 : Fin 2)) ?_⟩
  intro v w h
  exact False.elim (h.2 h.1)

/-- In particular, the set whose infimum defines the distance is nonempty. -/
theorem edgeDistancesToBipartite_nonempty (A : G.Subgraph) :
    (Erdos74.SimpleGraph.edgeDistancesToBipartite A).Nonempty := by
  exact ⟨A.edgeSet.ncard, A.edgeSet, Set.Subset.rfl,
    isBipartite_delete_all_edges A, rfl⟩

/-- The minimum deletion distance of a finite subgraph is attained by a finite edge set. -/
theorem minEdgeDistToBipartite_attained (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ E : Finset (Sym2 V), (E : Set (Sym2 V)) ⊆ A.edgeSet ∧
      IsBipartite (A.deleteEdges (E : Set (Sym2 V))).coe ∧
      E.card = Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  classical
  have hm := Nat.sInf_mem (edgeDistancesToBipartite_nonempty A)
  rcases hm with ⟨E, hE, hb, hc⟩
  have hfin : E.Finite := (edgeSet_finite_of_verts_finite A hA).subset hE
  refine ⟨hfin.toFinset, by simpa using hE, ?_, ?_⟩
  · exact hfin.coe_toFinset.symm ▸ hb
  · rw [← Set.ncard_eq_toFinset_card E hfin]
    exact hc

/-- An ambient edge set with `n` vertices has at most `n.choose 2` edges. -/
theorem subgraph_edgeSet_ncard_le_choose (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.ncard ≤ A.verts.ncard.choose 2 := by
  classical
  letI := hA.fintype
  have he : A.edgeSet.ncard = A.coe.edgeFinset.card := by
    rw [← A.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    exact Set.ncard_eq_toFinset_card' _
  have hv : A.verts.ncard = Fintype.card A.verts := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [he, hv]
  exact A.coe.card_edgeFinset_le_card_choose_two

/-- A uniform bound on all finite-subgraph deletion distances. -/
theorem minEdgeDistToBipartite_le_choose (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.verts.ncard.choose 2 := by
  have hle : Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.edgeSet.ncard :=
    Nat.sInf_le ⟨A.edgeSet, Set.Subset.rfl, isBipartite_delete_all_edges A, rfl⟩
  exact hle.trans (subgraph_edgeSet_ncard_le_choose A hA)

/-- The set defining the supremum at each fixed vertex count is bounded above. -/
theorem subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨A, hcard, hfin, rfl⟩
  simpa [hcard] using minEdgeDistToBipartite_le_choose A hfin

/-- Each finite subgraph's minimum is at most the specification's maximum at its order. -/
theorem minEdgeDistToBipartite_le_max (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤
      Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G A.verts.ncard := by
  exact le_csSup (subgraphEdgeDistsToBipartite_bddAbove G A.verts.ncard)
    ⟨A, rfl, hA, rfl⟩

/-- A bound from `Spec` supplies an actual finite edge-deletion budget for every finite subgraph. -/
theorem edgeDeletionBudget (G : SimpleGraph V) (f : ℕ → ℕ)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ E : Finset (Sym2 V), (E : Set (Sym2 V)) ⊆ A.edgeSet ∧
      IsBipartite (A.deleteEdges (E : Set (Sym2 V))).coe ∧
      E.card ≤ f A.verts.ncard := by
  obtain ⟨E, hE, hb, hc⟩ := minEdgeDistToBipartite_attained A hA
  refine ⟨E, hE, hb, ?_⟩
  rw [hc]
  exact (minEdgeDistToBipartite_le_max A hA).trans (hG A.verts.ncard)

/-- A coloring after edge deletion extends to a Boolean cut of the full ambient type.
Every monochromatic edge of the original subgraph belongs to the deleted set. -/
theorem exists_boolCut_of_deleteEdges_isBipartite (A : G.Subgraph)
    (E : Set (Sym2 V)) (hb : IsBipartite (A.deleteEdges E).coe) :
    ∃ p : V → Bool, ∀ ⦃u v : V⦄, A.Adj u v → p u = p v → s(u, v) ∈ E := by
  classical
  let c : (A.deleteEdges E).coe.Coloring Bool := hb.toColoring (by decide)
  let p : V → Bool := fun v ↦ if hv : v ∈ A.verts then c ⟨v, hv⟩ else false
  refine ⟨p, ?_⟩
  intro u v huv hp
  by_contra he
  have hu : u ∈ A.verts := A.edge_vert huv
  have hv : v ∈ A.verts := A.edge_vert huv.symm
  have hadj : (A.deleteEdges E).coe.Adj ⟨u, hu⟩ ⟨v, hv⟩ := ⟨huv, he⟩
  apply c.valid hadj
  simpa only [p, dif_pos hu, dif_pos hv] using hp

/-- Restrict an ambient cut to a finite subgraph's vertex type.  The injective map on
unordered vertex pairs ensures that no extra bad edges are counted after restriction. -/
theorem coeSubgraph_cut_of_deleteEdges_isBipartite (A : G.Subgraph) [Fintype A.verts]
    (H : A.coe.Subgraph) (E : Finset (Sym2 V))
    (hb : IsBipartite ((Subgraph.coeSubgraph H).deleteEdges (E : Set (Sym2 V))).coe) :
    ∃ p : A.verts → Bool, (badEdges H.spanningCoe p).card ≤ E.card := by
  classical
  obtain ⟨p, hp⟩ := exists_boolCut_of_deleteEdges_isBipartite
    (Subgraph.coeSubgraph H) (E : Set (Sym2 V)) hb
  refine ⟨fun v ↦ p v, ?_⟩
  apply Finset.card_le_card_of_injOn (Sym2.map (Subtype.val : A.verts → V))
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨huv, heq⟩ := (mem_badEdges H.spanningCoe (fun v ↦ p v) u v).mp he
      change s((u : V), (v : V)) ∈ E
      apply hp ?_ heq
      exact (Subgraph.coeSubgraph_adj H u v).mpr ⟨u.property, v.property, huv⟩
  · exact (Sym2.map.injective Subtype.val_injective).injOn

/-- The parametric bridge from `Spec`'s numerical bound to `E74.SmallCuts` on every
finite subgraph.  No finiteness assumption is imposed on the ambient vertex type. -/
theorem smallCuts_of_maxSubgraphEdgeDistToBipartite (B f : ℕ → ℕ)
    (hf : ∀ k, 2 ≤ k → ∀ n, n ≤ B k → f n < k)
    (G : SimpleGraph V)
    (hG : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    letI := hA.fintype
    SmallCuts A.coe B := by
  classical
  letI := hA.fintype
  intro k hk H hH
  have hfin : (Subgraph.coeSubgraph H).verts.Finite :=
    (Set.toFinite H.verts).image (Subtype.val : A.verts → V)
  have hn : (Subgraph.coeSubgraph H).verts.ncard = H.verts.ncard :=
    Set.ncard_image_of_injective H.verts Subtype.val_injective
  obtain ⟨E, _, hb, hcard⟩ := edgeDeletionBudget G f hG (Subgraph.coeSubgraph H) hfin
  obtain ⟨p, hp⟩ := coeSubgraph_cut_of_deleteEdges_isBipartite A H E hb
  refine ⟨p, hp.trans_lt ?_⟩
  rw [hn] at hcard
  exact hcard.trans_lt (hf k hk H.verts.ncard hH)

end E74
