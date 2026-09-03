import FormalConjecturesUtil

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

/-
## Bridges from the profile definitions to finite edge-deletion witnesses

Only the four definitions above are copied from `Spec`. The lemmas below can
be pasted immediately after those definitions in `Spec` (inside `Erdos74`).
No finiteness assumption on the ambient vertex type is used.
-/

namespace SimpleGraph

variable {G : _root_.SimpleGraph V}

/-- Every edge comes from an ordered pair of vertices of the subgraph. -/
theorem Subgraph.edgeSet_subset_verts_prod_image (A : G.Subgraph) :
    A.edgeSet ⊆ Sym2.mk '' (A.verts ×ˢ A.verts) := by
  intro e he
  induction e using Sym2.ind with
  | h v w => exact ⟨(v, w), ⟨A.edge_vert he, A.edge_vert (A.symm he)⟩, rfl⟩

/-- Finite vertex sets have finite edge sets, even in an infinite ambient graph. -/
theorem Subgraph.edgeSet_finite_of_verts_finite (A : G.Subgraph)
    (hA : A.verts.Finite) : A.edgeSet.Finite :=
  ((hA.prod hA).image Sym2.mk).subset (Subgraph.edgeSet_subset_verts_prod_image A)

/-- A deliberately coarse bound that avoids any ordering on the vertex type. -/
theorem Subgraph.edgeSet_ncard_le_verts_ncard_sq (A : G.Subgraph)
    (hA : A.verts.Finite) : A.edgeSet.ncard ≤ A.verts.ncard ^ 2 := by
  calc
    A.edgeSet.ncard ≤ (Sym2.mk '' (A.verts ×ˢ A.verts)).ncard :=
      Set.ncard_le_ncard (Subgraph.edgeSet_subset_verts_prod_image A)
        ((hA.prod hA).image Sym2.mk)
    _ ≤ (A.verts ×ˢ A.verts).ncard := Set.ncard_image_le (hA.prod hA)
    _ = A.verts.ncard ^ 2 := by rw [Set.ncard_prod, pow_two]

/-- Deleting every edge leaves the edgeless graph on the same vertex set. -/
@[simp] theorem Subgraph.coe_deleteEdges_edgeSet (A : G.Subgraph) :
    (A.deleteEdges A.edgeSet).coe = ⊥ := by
  ext v w
  simp

/-- Deleting every edge is always a bipartite-deletion witness. -/
theorem Subgraph.isBipartite_deleteEdges_edgeSet (A : G.Subgraph) :
    (A.deleteEdges A.edgeSet).coe.IsBipartite := by
  rw [Subgraph.coe_deleteEdges_edgeSet]
  exact ⟨Coloring.mk (fun _ => (0 : Fin 2)) (by simp)⟩

/-- The edge count is an admissible deletion distance, without a finiteness hypothesis. -/
theorem edgeSet_ncard_mem_edgeDistancesToBipartite (A : G.Subgraph) :
    A.edgeSet.ncard ∈ edgeDistancesToBipartite A :=
  ⟨A.edgeSet, Set.Subset.rfl, Subgraph.isBipartite_deleteEdges_edgeSet A, rfl⟩

/-- The infimum in the definition is taken over a nonempty set. -/
theorem edgeDistancesToBipartite_nonempty (A : G.Subgraph) :
    (edgeDistancesToBipartite A).Nonempty :=
  ⟨_, edgeSet_ncard_mem_edgeDistancesToBipartite A⟩

/-- The natural-number infimum is attained. -/
theorem minEdgeDistToBipartite_mem (A : G.Subgraph) :
    minEdgeDistToBipartite A ∈ edgeDistancesToBipartite A :=
  Nat.sInf_mem (edgeDistancesToBipartite_nonempty A)

/-- For a finite subgraph, the attained minimum has a genuinely finite witness. -/
theorem exists_set_ncard_eq_minEdgeDistToBipartite (A : G.Subgraph)
    (hA : A.verts.Finite) :
    ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧ E.Finite ∧
      E.ncard = minEdgeDistToBipartite A ∧ (A.deleteEdges E).coe.IsBipartite := by
  obtain ⟨E, hE, hbip, hcard⟩ := minEdgeDistToBipartite_mem A
  exact ⟨E, hE, (Subgraph.edgeSet_finite_of_verts_finite A hA).subset hE, hcard, hbip⟩

/-- Every admissible deletion witness bounds the minimum from above. -/
theorem minEdgeDistToBipartite_le_ncard (A : G.Subgraph) {E : Set (Sym2 V)}
    (hE : E ⊆ A.edgeSet) (hbip : (A.deleteEdges E).coe.IsBipartite) :
    minEdgeDistToBipartite A ≤ E.ncard :=
  Nat.sInf_le ⟨E, hE, hbip, rfl⟩

/-- Deleting all edges bounds the minimum by the edge count. -/
theorem minEdgeDistToBipartite_le_edgeSet_ncard (A : G.Subgraph) :
    minEdgeDistToBipartite A ≤ A.edgeSet.ncard :=
  Nat.sInf_le (edgeSet_ncard_mem_edgeDistancesToBipartite A)

/-- A finite subgraph's minimum deletion distance is at most its squared order. -/
theorem minEdgeDistToBipartite_le_verts_ncard_sq (A : G.Subgraph)
    (hA : A.verts.Finite) : minEdgeDistToBipartite A ≤ A.verts.ncard ^ 2 :=
  (minEdgeDistToBipartite_le_edgeSet_ncard A).trans
    (Subgraph.edgeSet_ncard_le_verts_ncard_sq A hA)

/-- Every member of the size-`n` profile set is bounded by `n ^ 2`. -/
theorem subgraphEdgeDistsToBipartite_le_sq {n k : ℕ}
    (hk : k ∈ subgraphEdgeDistsToBipartite G n) : k ≤ n ^ 2 := by
  obtain ⟨A, hn, hA, rfl⟩ := hk
  simpa only [hn] using minEdgeDistToBipartite_le_verts_ncard_sq A hA

/-- The supremum in the profile definition has the explicit upper bound `n ^ 2`. -/
theorem subgraphEdgeDistsToBipartite_bddAbove (G : _root_.SimpleGraph V) (n : ℕ) :
    BddAbove (subgraphEdgeDistsToBipartite G n) :=
  ⟨n ^ 2, fun _ hk => subgraphEdgeDistsToBipartite_le_sq hk⟩

/-- This also covers sizes for which the graph has no subgraph: `sSup ∅ = 0`. -/
theorem maxSubgraphEdgeDistToBipartite_le_sq (G : _root_.SimpleGraph V) (n : ℕ) :
    maxSubgraphEdgeDistToBipartite G n ≤ n ^ 2 :=
  csSup_le' (fun _ hk => subgraphEdgeDistsToBipartite_le_sq hk)

/-- A finite subgraph's distance is below the ambient profile at its vertex count. -/
theorem minEdgeDistToBipartite_le_maxSubgraphEdgeDistToBipartite (A : G.Subgraph)
    (hA : A.verts.Finite) :
    minEdgeDistToBipartite A ≤ maxSubgraphEdgeDistToBipartite G A.verts.ncard :=
  le_csSup (subgraphEdgeDistsToBipartite_bddAbove G A.verts.ncard) ⟨A, rfl, hA, rfl⟩

/-- A minimum-distance bound is equivalent to a finite edge-deletion witness. -/
theorem minEdgeDistToBipartite_le_iff (A : G.Subgraph) (hA : A.verts.Finite) (k : ℕ) :
    minEdgeDistToBipartite A ≤ k ↔
      ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧ E.Finite ∧
        E.ncard ≤ k ∧ (A.deleteEdges E).coe.IsBipartite := by
  constructor
  · intro h
    obtain ⟨E, hE, hfin, hcard, hbip⟩ := exists_set_ncard_eq_minEdgeDistToBipartite A hA
    exact ⟨E, hE, hfin, hcard.le.trans h, hbip⟩
  · rintro ⟨E, hE, _, hcard, hbip⟩
    exact (minEdgeDistToBipartite_le_ncard A hE hbip).trans hcard

/-- The main set-valued bridge: a profile bound supplies actual finite deletions. -/
theorem exists_finite_bipartite_deletion_of_profile_le {f : ℕ → ℕ}
    (hG : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧ E.Finite ∧
      E.ncard ≤ f A.verts.ncard ∧ (A.deleteEdges E).coe.IsBipartite :=
  (minEdgeDistToBipartite_le_iff A hA _).mp
    ((minEdgeDistToBipartite_le_maxSubgraphEdgeDistToBipartite A hA).trans (hG _))

/-- A `Finset` version of the main bridge, with an ordinary `Finset.card` bound. -/
theorem exists_finset_bipartite_deletion_of_profile_le {f : ℕ → ℕ}
    (hG : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ E : Finset (Sym2 V), (E : Set (Sym2 V)) ⊆ A.edgeSet ∧
      E.card ≤ f A.verts.ncard ∧ (A.deleteEdges (E : Set (Sym2 V))).coe.IsBipartite := by
  obtain ⟨E, hE, hfin, hcard, hbip⟩ := exists_finite_bipartite_deletion_of_profile_le hG A hA
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · simpa only [Set.Finite.coe_toFinset] using hE
  · simpa only [Set.ncard_eq_toFinset_card E hfin] using hcard
  · rw [hfin.coe_toFinset]
    exact hbip

/-- Conversely, actual deletion witnesses imply the profile bound, including at empty sizes. -/
theorem profile_le_iff_finite_bipartite_deletion (G : _root_.SimpleGraph V) (f : ℕ → ℕ) :
    (∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n) ↔
      ∀ (A : G.Subgraph), A.verts.Finite →
        ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧ E.Finite ∧
          E.ncard ≤ f A.verts.ncard ∧ (A.deleteEdges E).coe.IsBipartite := by
  constructor
  · exact fun hG A hA => exists_finite_bipartite_deletion_of_profile_le hG A hA
  · intro hG n
    apply csSup_le'
    rintro k ⟨A, hn, hA, rfl⟩
    simpa only [hn] using (minEdgeDistToBipartite_le_iff A hA _).mpr (hG A hA)

universe v

/-- An injective graph homomorphism cannot decrease the deletion distance of a subgraph.
No finiteness hypothesis is needed here, since the pulled-back edge set has the same `ncard`. -/
theorem minEdgeDistToBipartite_le_map_of_injective_hom
    {W : Type v} {H : _root_.SimpleGraph W} (φ : H →g G)
    (hφ : Function.Injective φ) (A : H.Subgraph) :
    minEdgeDistToBipartite A ≤ minEdgeDistToBipartite (A.map φ) := by
  obtain ⟨E, hE, hbip, hcard⟩ := minEdgeDistToBipartite_mem (A.map φ)
  have hφ₂ : Function.Injective (Sym2.map φ) := Sym2.map.injective hφ
  have hpre : Sym2.map φ ⁻¹' E ⊆ A.edgeSet := by
    intro e he
    have hm := hE he
    rw [_root_.SimpleGraph.Subgraph.edgeSet_map] at hm
    obtain ⟨e', he', heq⟩ := hm
    exact hφ₂ heq ▸ he'
  have hrange : E ⊆ Set.range (Sym2.map φ) := by
    intro e he
    have hm := hE he
    rw [_root_.SimpleGraph.Subgraph.edgeSet_map] at hm
    exact Set.image_subset_range _ _ hm
  let ψ : (A.deleteEdges (Sym2.map φ ⁻¹' E)).coe →g ((A.map φ).deleteEdges E).coe :=
    { toFun := fun v => ⟨φ v.1, ⟨v.1, v.2, rfl⟩⟩
      map_rel' := by
        intro v w hvw
        exact ⟨⟨v.1, w.1, hvw.1, rfl, rfl⟩, hvw.2⟩ }
  calc
    minEdgeDistToBipartite A ≤ (Sym2.map φ ⁻¹' E).ncard :=
      minEdgeDistToBipartite_le_ncard A hpre (hbip.of_hom ψ)
    _ = E.ncard := Set.ncard_preimage_of_injective_subset_range hφ₂ hrange
    _ = minEdgeDistToBipartite (A.map φ) := hcard

/-- The profile is monotone under injective graph homomorphisms, even across universes. -/
theorem maxSubgraphEdgeDistToBipartite_mono_of_injective_hom
    {W : Type v} {H : _root_.SimpleGraph W} (φ : H →g G)
    (hφ : Function.Injective φ) (n : ℕ) :
    maxSubgraphEdgeDistToBipartite H n ≤ maxSubgraphEdgeDistToBipartite G n := by
  apply csSup_le'
  rintro k ⟨A, hn, hA, rfl⟩
  have hfin : (A.map φ).verts.Finite := hA.image φ
  have hn' : (A.map φ).verts.ncard = n :=
    (Set.ncard_image_of_injective A.verts hφ).trans hn
  have hle := (minEdgeDistToBipartite_le_map_of_injective_hom φ hφ A).trans
    (minEdgeDistToBipartite_le_maxSubgraphEdgeDistToBipartite (A.map φ) hfin)
  simpa only [hn'] using hle

/-- Every subgraph, viewed on its own vertex type, inherits the ambient profile bound. -/
theorem maxSubgraphEdgeDistToBipartite_coe_le (A : G.Subgraph) (n : ℕ) :
    maxSubgraphEdgeDistToBipartite A.coe n ≤ maxSubgraphEdgeDistToBipartite G n :=
  maxSubgraphEdgeDistToBipartite_mono_of_injective_hom A.hom
    _root_.SimpleGraph.Subgraph.hom_injective n

/-- Compactness packaged in terms of `Colorable`, for any fixed finite palette. -/
theorem colorable_of_forall_finite_subgraph_colorable (G : _root_.SimpleGraph V) (k : ℕ)
    (hG : ∀ A : G.Subgraph, A.verts.Finite → A.coe.Colorable k) : G.Colorable k := by
  classical
  exact nonempty_hom_of_forall_finite_subgraph_hom (fun A hA => (hG A hA).some)

/-- A finite-graph coloring theorem for a local profile extends to arbitrary graphs.
The finite vertex types are allowed to live in the same arbitrary universe as `V`. -/
theorem colorable_of_profile_le_of_finite {f : ℕ → ℕ} {k : ℕ}
    (hfinite : ∀ (W : Type u) [Finite W] (H : _root_.SimpleGraph W),
      (∀ n, maxSubgraphEdgeDistToBipartite H n ≤ f n) → H.Colorable k)
    (hG : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n) : G.Colorable k := by
  apply colorable_of_forall_finite_subgraph_colorable G k
  intro A hA
  letI : Finite A.verts := hA.to_subtype
  exact hfinite A.verts A.coe
    (fun n => (maxSubgraphEdgeDistToBipartite_coe_le A n).trans (hG n))

/-- In particular, any fixed finite-colorability conclusion rules out infinite chromatic number. -/
theorem chromaticNumber_ne_top_of_profile_le_of_finite {f : ℕ → ℕ} {k : ℕ}
    (hfinite : ∀ (W : Type u) [Finite W] (H : _root_.SimpleGraph W),
      (∀ n, maxSubgraphEdgeDistToBipartite H n ≤ f n) → H.Colorable k)
    (hG : ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n) : G.chromaticNumber ≠ ⊤ :=
  _root_.SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr
    ⟨k, colorable_of_profile_le_of_finite hfinite hG⟩

/-- A generic contradiction principle, independent of the original conjecture's theorem.
For example, set `k = 3` after proving a finite-graph three-colorability theorem
for some divergent budget `f`. Divergence is needed only to instantiate the
universally quantified assertion, not for compactness itself. -/
theorem not_forall_exists_infinite_chromatic_profile {f : ℕ → ℕ} {k : ℕ}
    (hf : Tendsto f atTop atTop)
    (hfinite : ∀ (W : Type u) [Finite W] (H : _root_.SimpleGraph W),
      (∀ n, maxSubgraphEdgeDistToBipartite H n ≤ f n) → H.Colorable k) :
    ¬ (∀ g : ℕ → ℕ, Tendsto g atTop atTop →
      ∃ (W : Type u) (H : _root_.SimpleGraph W), H.chromaticNumber = ⊤ ∧
        ∀ n, maxSubgraphEdgeDistToBipartite H n ≤ g n) := by
  intro h
  obtain ⟨W, H, hχ, hH⟩ := h f hf
  exact chromaticNumber_ne_top_of_profile_le_of_finite hfinite hH hχ

end SimpleGraph

end Erdos74
