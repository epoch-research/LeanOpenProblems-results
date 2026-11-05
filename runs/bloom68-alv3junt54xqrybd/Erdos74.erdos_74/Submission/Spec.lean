import FormalConjecturesUtil
import Submission.Pressure
import Submission.Budget

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?
-/
theorem erdos_74 : ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) := by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74

namespace Erdos74.Integration

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A subgraph on finitely many actual vertices has finitely many actual edges. -/
lemma finite_edgeSet (A : G.Subgraph) (hA : A.verts.Finite) : A.edgeSet.Finite := by
  classical
  letI := hA.fintype
  rw [← A.image_coe_edgeSet_coe]
  exact (Set.toFinite A.coe.edgeSet).image _

lemma delete_all_bipartite (A : G.Subgraph) : (A.deleteEdges A.edgeSet).coe.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) ?_⟩
  intro v w h
  exact (h.2 h.1).elim

lemma distance_set_nonempty (A : G.Subgraph) :
    (Erdos74.SimpleGraph.edgeDistancesToBipartite A).Nonempty := by
  exact ⟨_, A.edgeSet, Set.Subset.rfl, delete_all_bipartite A, rfl⟩

lemma min_dist_attained (A : G.Subgraph) :
    ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧ (A.deleteEdges E).coe.IsBipartite ∧
      E.ncard = Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  obtain ⟨E, hE, hB, hcard⟩ := Nat.sInf_mem (distance_set_nonempty A)
  exact ⟨E, hE, hB, hcard⟩

lemma min_dist_le_edges (A : G.Subgraph) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤ A.edgeSet.ncard := by
  exact Nat.sInf_le ⟨A.edgeSet, Set.Subset.rfl, delete_all_bipartite A, rfl⟩

lemma edges_le_choose (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.ncard ≤ A.verts.ncard.choose 2 := by
  classical
  letI := hA.fintype
  rw [← A.image_coe_edgeSet_coe,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  have hcard : Fintype.card A.verts = A.verts.ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hle := Set.ncard_le_ncard A.coe.edgeSet_subset_setOf_not_isDiag
  have hdiag : (Sym2.diagSetᶜ : Set (Sym2 A.verts)).ncard = A.verts.ncard.choose 2 := by
    change Nat.card (Sym2.diagSetᶜ : Set (Sym2 A.verts)) = _
    rw [Nat.card_eq_fintype_card, Sym2.card_diagSet_compl, hcard]
  exact hle.trans_eq hdiag

lemma subgraph_distances_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro k ⟨A, hcard, hfinite, rfl⟩
  exact (min_dist_le_edges A).trans (hcard ▸ edges_le_choose A hfinite)

lemma min_dist_le_max (A : G.Subgraph) (hA : A.verts.Finite) :
    Erdos74.SimpleGraph.minEdgeDistToBipartite A ≤
      Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G A.verts.ncard := by
  exact le_csSup (subgraph_distances_bddAbove G _) ⟨A, rfl, hA, rfl⟩

/-- Compactness supplies a finite subgraph that is not three-colorable. -/
lemma exists_finite_not_colorable (hG : G.chromaticNumber = ⊤) (k : ℕ) :
    ∃ A : G.Subgraph, A.verts.Finite ∧ ¬ A.coe.Colorable k := by
  classical
  by_contra h
  push_neg at h
  have hc : G.Colorable k :=
    SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom (fun A hA => (h A hA).some)
  have hle := hc.chromaticNumber_le
  simp [hG] at hle

/-- A bipartizing deletion yields a binary cut whose defects inject into the
actual deleted edge set. This uses finiteness, rather than the junk `ncard` of
an infinite set. -/
lemma tau_le_min_dist (A : G.Subgraph) [Finite A.verts] (hA : A.verts.Finite) :
    E74.tau A.coe ≤ Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  classical
  obtain ⟨E, hE, ⟨c⟩, hcard⟩ := min_dist_attained A
  have hEf : E.Finite := (finite_edgeSet A hA).subset hE
  let b : A.verts → Bool := fun x => finTwoEquiv (c x)
  have hcost : E74.cost A.coe b ≤ E.ncard := by
    rw [E74.cost, Set.ncard_eq_toFinset_card E hEf]
    apply Finset.card_le_card_of_injOn (Sym2.map (Subtype.val : A.verts → V))
    · intro e he
      apply hEf.mem_toFinset.mpr
      revert he
      refine Sym2.ind ?_ e
      intro x y he
      obtain ⟨hxy, hm⟩ := (E74.mk_mem_defects A.coe b x y).mp he
      by_contra hn
      have ha : (A.deleteEdges E).coe.Adj x y := ⟨hxy, hn⟩
      exact c.valid ha (finTwoEquiv.injective hm)
    · exact (Sym2.map.injective Subtype.val_injective).injOn
  exact (E74.tau_le_cost A.coe b).trans (hcost.trans_eq hcard)

/-- Adding edges cannot decrease the minimum binary-cut cost. -/
lemma tau_mono [Finite V] {H K : SimpleGraph V} (hHK : H ≤ K) :
    E74.tau H ≤ E74.tau K := by
  classical
  obtain ⟨b, hb⟩ := E74.tau_attained K
  have hs : E74.defects H b ⊆ E74.defects K b := by
    intro e
    refine Sym2.ind ?_ e
    intro x y he
    obtain ⟨ha, hm⟩ := (E74.mk_mem_defects H b x y).mp he
    exact (E74.mk_mem_defects K b x y).mpr ⟨hHK ha, hm⟩
  exact (E74.tau_le_cost H b).trans ((Finset.card_le_card hs).trans_eq hb)

/-- Flattening a set of subgraph vertices preserves the actual induced graph. -/
noncomputable def ambientInduceIso (A : G.Subgraph) (S : Set A.verts) :
    A.coe.induce S ≃g (A.induce ((Subtype.val : A.verts → V) '' S)).coe where
  toEquiv := Equiv.Set.image (Subtype.val : A.verts → V) S Subtype.val_injective
  map_rel_iff' := by
    intro x y
    change (x.val.val ∈ (Subtype.val : A.verts → V) '' S ∧
      y.val.val ∈ (Subtype.val : A.verts → V) '' S ∧ A.Adj x.val.val y.val.val) ↔
      A.Adj x.val.val y.val.val
    exact ⟨fun h => h.2.2,
      fun h => ⟨⟨x.val, x.property, rfl⟩, ⟨y.val, y.property, rfl⟩, h⟩⟩

end Erdos74.Integration

theorem Erdos74.erdos_74.disproof : ¬ (type_of% @Erdos74.erdos_74) := by
  classical
  intro h
  obtain ⟨V, G, hchi, hprofile⟩ := h E74.slowBudget E74.slowBudget_tendsto
  obtain ⟨A, hA, hnoncol⟩ := Erdos74.Integration.exists_finite_not_colorable hchi 3
  letI := hA.fintype
  obtain ⟨S, k, hS, hk, H, hH, hktau, hsize⟩ :=
    E74.pressure_certificate A.coe (E74.pressure_of_not_colorable A.coe hnoncol)
  let T : Set V := (Subtype.val : A.verts → V) '' S
  let B : G.Subgraph := A.induce T
  have hB : B.verts.Finite := hS.image Subtype.val
  letI := hB.fintype
  have hcard : B.verts.ncard = S.ncard :=
    Set.ncard_image_of_injective S Subtype.val_injective
  have hcost : k ≤ E74.tau B.coe := by
    calc
      k ≤ E74.tau H := hktau
      _ ≤ E74.tau (A.coe.induce S) := Erdos74.Integration.tau_mono hH
      _ = E74.tau B.coe := E74.PressureProof.tau_iso
        (Erdos74.Integration.ambientInduceIso A S)
  have hbound : k ≤ E74.slowBudget B.verts.ncard :=
    hcost.trans ((Erdos74.Integration.tau_le_min_dist B hB).trans
      ((Erdos74.Integration.min_dist_le_max B hB).trans (hprofile B.verts.ncard)))
  have hlt : E74.slowBudget B.verts.ncard < k :=
    E74.slowBudget_lt hk (hcard ▸ hsize)
  exact (Nat.not_le_of_lt hlt) hbound

