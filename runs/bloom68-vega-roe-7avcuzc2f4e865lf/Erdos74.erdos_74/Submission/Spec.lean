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

/-
## Finite certificates for distance from bipartiteness

For each positive integer `k` we construct a graph-independent finite threshold.
Every finite graph which is not three-colorable has a finite edge set below one
of these thresholds on which every Boolean coloring has at least `k`
monochromatic edges. A sufficiently slowly divergent function lies below `k`
on all corresponding endpoint sets. Thus its profile bound forces every finite
subgraph to be three-colorable; finite-color compactness rules out infinite
chromatic number.

The certificate theorem uses strong induction on the number of bad edges of an
arbitrary Boolean coloring. A small-error coloring of a ball can be repaired
recursively and glued to the old coloring across a four-level annulus. Otherwise
a bounded walk cover, representative edge constraints, and finite branching
produce the required finite certificate.
-/

namespace Erdos74

universe u
variable {V : Type u}

/-
## Bridges from the profile definitions to finite edge-deletion witnesses

These lemmas connect the profile to actual finite bipartizing deletions.
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

/-
# Finite edge certificates for Erdős problem 74

Endpoints, monochromatic edges, and their behavior under deletion, vertex maps,
and restriction to induced subgraphs. These lemmas use Boolean colorings directly,
without choosing a minimum bipartizing deletion.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

noncomputable def endVerts (E : Finset (Sym2 V)) : Finset V := by
  classical
  exact E.biUnion Sym2.toFinset

def mono (d : V → Bool) (e : Sym2 V) : Prop := (e.map d).IsDiag

@[simp] theorem mono_pair (d : V → Bool) (v w : V) :
    mono d s(v,w) ↔ d v = d w := by
  simp [mono]

def badGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v = c w
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun v h => G.loopless v h.1

noncomputable def badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool) :
    Finset (Sym2 V) := (badGraph G c).edgeSet.toFinite.toFinset

@[simp] theorem mem_badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool)
    (v w : V) : s(v,w) ∈ badEdges G c ↔ G.Adj v w ∧ c v = c w := by
  simp [badEdges, SimpleGraph.mem_edgeSet, badGraph]

/- ## Endpoints of finite edge sets -/

@[simp] theorem mem_endVerts {E : Finset (Sym2 V)} {v : V} :
    v ∈ endVerts E ↔ ∃ e ∈ E, v ∈ e := by
  classical
  simp [endVerts]

theorem mem_endVerts_iff {E : Finset (Sym2 V)} {v : V} :
    v ∈ endVerts E ↔ ∃ w, s(v,w) ∈ E := by
  simp only [mem_endVerts, Sym2.mem_iff_exists]
  constructor
  · rintro ⟨e, he, w, rfl⟩
    exact ⟨w, he⟩
  · rintro ⟨w, hw⟩
    exact ⟨s(v,w), hw, w, rfl⟩

theorem left_mem_endVerts {E : Finset (Sym2 V)} {v w : V}
    (h : s(v,w) ∈ E) : v ∈ endVerts E :=
  mem_endVerts_iff.mpr ⟨w, h⟩

theorem right_mem_endVerts {E : Finset (Sym2 V)} {v w : V}
    (h : s(v,w) ∈ E) : w ∈ endVerts E :=
  mem_endVerts.mpr ⟨s(v,w), h, Sym2.mem_mk_right v w⟩

theorem endVerts_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) :
    endVerts E ⊆ endVerts F := by
  rintro v hv
  obtain ⟨e, he, hv⟩ := mem_endVerts.mp hv
  exact mem_endVerts.mpr ⟨e, h he, hv⟩

@[simp] theorem endVerts_empty : endVerts (∅ : Finset (Sym2 V)) = ∅ := by
  classical
  simp [endVerts]

theorem endVerts_union (E F : Finset (Sym2 V)) [DecidableEq (Sym2 V)]
    [DecidableEq V] : endVerts (E ∪ F) = endVerts E ∪ endVerts F := by
  ext v
  simp only [mem_endVerts, Finset.mem_union]
  aesop

theorem card_endVerts_le (E : Finset (Sym2 V)) :
    (endVerts E).card ≤ 2 * E.card := by
  classical
  simpa only [endVerts, Nat.mul_comm] using
    (Finset.card_biUnion_le_card_mul E Sym2.toFinset 2 (by
      intro e _
      rw [Sym2.card_toFinset]
      split_ifs <;> omega))

/- ## Boolean colorings and monochromatic edges -/

instance instDecidableMono (d : V → Bool) (e : Sym2 V) : Decidable (mono d e) :=
  inferInstanceAs (Decidable (e.map d).IsDiag)

theorem mem_badEdges_iff [Finite V] (G : SimpleGraph V) (c : V → Bool)
    (e : Sym2 V) : e ∈ badEdges G c ↔ e ∈ G.edgeSet ∧ mono c e := by
  induction e using Sym2.ind with
  | h v w => simp

theorem badEdges_subset_edgeSet [Finite V] (G : SimpleGraph V) (c : V → Bool) :
    (badEdges G c : Set (Sym2 V)) ⊆ G.edgeSet := by
  intro e he
  exact ((mem_badEdges_iff G c e).mp he).1

theorem filter_mono_subset_badEdges [Finite V] (G : SimpleGraph V)
    (c : V → Bool) {Q : Finset (Sym2 V)} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) :
    Q.filter (mono c) ⊆ badEdges G c := by
  intro e he
  obtain ⟨heQ, hec⟩ := Finset.mem_filter.mp he
  exact (mem_badEdges_iff G c e).mpr ⟨hQ heQ, hec⟩

theorem card_filter_mono_le_badEdges [Finite V] (G : SimpleGraph V)
    (c : V → Bool) {Q : Finset (Sym2 V)} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) :
    (Q.filter (mono c)).card ≤ (badEdges G c).card :=
  Finset.card_le_card (filter_mono_subset_badEdges G c hQ)

/-- A proper Boolean coloring is a bipartite coloring, with no finiteness assumptions. -/
theorem isBipartite_of_bool_coloring {G : SimpleGraph V} (c : V → Bool)
    (hc : ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w) : G.IsBipartite := by
  simpa using (SimpleGraph.Coloring.mk c (fun h => hc h)).colorable

theorem exists_bool_coloring_of_isBipartite {G : SimpleGraph V} (hG : G.IsBipartite) :
    ∃ c : V → Bool, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w := by
  let c : G.Coloring Bool := hG.toColoring (by simp)
  exact ⟨c, fun _ _ h => c.valid h⟩

theorem isBipartite_iff_exists_bool_coloring (G : SimpleGraph V) :
    G.IsBipartite ↔ ∃ c : V → Bool, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w :=
  ⟨exists_bool_coloring_of_isBipartite, fun ⟨c, hc⟩ => isBipartite_of_bool_coloring c hc⟩

theorem isBipartite_iff_nonempty_boolColoring (G : SimpleGraph V) :
    G.IsBipartite ↔ Nonempty (G.Coloring Bool) := by
  constructor
  · intro h
    exact ⟨h.toColoring (by simp)⟩
  · rintro ⟨c⟩
    exact isBipartite_of_bool_coloring c (fun _ _ h => c.valid h)

/-- A fixed coloring is proper after deletion exactly when all its bad edges are deleted. -/
theorem proper_deleteEdges_iff_badEdges_subset [Finite V] (G : SimpleGraph V)
    (c : V → Bool) (E : Set (Sym2 V)) :
    (∀ ⦃v w : V⦄, (G.deleteEdges E).Adj v w → c v ≠ c w) ↔
      (badEdges G c : Set (Sym2 V)) ⊆ E := by
  constructor
  · intro hc e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨hadj, heq⟩ := (mem_badEdges G c v w).mp he
      by_contra hE
      exact hc (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hE⟩) heq
  · intro hE v w hvw heq
    obtain ⟨hadj, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hvw
    exact hnot (hE ((mem_badEdges G c v w).mpr ⟨hadj, heq⟩))

theorem proper_delete_badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool)
    {v w : V} (h : (G.deleteEdges (badEdges G c : Set (Sym2 V))).Adj v w) :
    c v ≠ c w :=
  (proper_deleteEdges_iff_badEdges_subset G c _).mpr Set.Subset.rfl h

theorem isBipartite_delete_badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool) :
    (G.deleteEdges (badEdges G c : Set (Sym2 V))).IsBipartite :=
  isBipartite_of_bool_coloring c (fun _ _ h => proper_delete_badEdges G c h)

/-- One endpoint outside the endpoints of a set containing all bad edges suffices. -/
theorem proper_of_not_mem_endVerts [Finite V] {G : SimpleGraph V} {c : V → Bool}
    {F : Finset (Sym2 V)} (hF : badEdges G c ⊆ F) {v w : V}
    (hvw : G.Adj v w) (hv : v ∉ endVerts F) : c v ≠ c w := by
  intro heq
  exact hv (left_mem_endVerts (hF ((mem_badEdges G c v w).mpr ⟨hvw, heq⟩)))

theorem proper_off_badEdges [Finite V] {G : SimpleGraph V} {c : V → Bool}
    {v w : V} (hvw : G.Adj v w) (hv : v ∉ endVerts (badEdges G c)) : c v ≠ c w :=
  proper_of_not_mem_endVerts (fun _ h => h) hvw hv

theorem exists_badEdges_subset_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Set (Sym2 V)} (h : (G.deleteEdges E).IsBipartite) :
    ∃ c : V → Bool, (badEdges G c : Set (Sym2 V)) ⊆ E := by
  obtain ⟨c, hc⟩ := exists_bool_coloring_of_isBipartite h
  exact ⟨c, (proper_deleteEdges_iff_badEdges_subset G c E).mp hc⟩

theorem isBipartite_deleteEdges_iff_exists_badEdges_subset [Finite V]
    (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (G.deleteEdges E).IsBipartite ↔
      ∃ c : V → Bool, (badEdges G c : Set (Sym2 V)) ⊆ E := by
  constructor
  · exact exists_badEdges_subset_of_isBipartite_deleteEdges
  · rintro ⟨c, hc⟩
    exact isBipartite_of_bool_coloring c
      ((proper_deleteEdges_iff_badEdges_subset G c E).mpr hc)

theorem exists_badEdges_subset_finset_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : (G.deleteEdges (E : Set (Sym2 V))).IsBipartite) :
    ∃ c : V → Bool, badEdges G c ⊆ E :=
  exists_badEdges_subset_of_isBipartite_deleteEdges h

theorem exists_badEdges_card_le_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : (G.deleteEdges (E : Set (Sym2 V))).IsBipartite) :
    ∃ c : V → Bool, badEdges G c ⊆ E ∧ (badEdges G c).card ≤ E.card := by
  obtain ⟨c, hc⟩ := exists_badEdges_subset_finset_of_isBipartite_deleteEdges h
  exact ⟨c, hc, Finset.card_le_card hc⟩

theorem exists_badEdges_card_le_ncard_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Set (Sym2 V)} (hE : E.Finite)
    (h : (G.deleteEdges E).IsBipartite) :
    ∃ c : V → Bool, (badEdges G c : Set (Sym2 V)) ⊆ E ∧
      (badEdges G c).card ≤ E.ncard := by
  obtain ⟨c, hc⟩ := exists_badEdges_subset_of_isBipartite_deleteEdges h
  exact ⟨c, hc, by simpa using Set.ncard_le_ncard hc hE⟩

/- ## Transport along vertex maps -/

universe v
variable {W : Type v}

@[simp] theorem mono_map (f : V → W) (d : W → Bool) (e : Sym2 V) :
    mono d (e.map f) ↔ mono (d ∘ f) e := by
  simp only [mono, Sym2.map_map]

theorem card_image_edges_le [DecidableEq W] (f : V → W) (Q : Finset (Sym2 V)) :
    (Q.image (Sym2.map f)).card ≤ Q.card :=
  Finset.card_image_le

theorem card_image_edges [DecidableEq W] (f : V → W) (hf : Function.Injective f)
    (Q : Finset (Sym2 V)) : (Q.image (Sym2.map f)).card = Q.card :=
  Finset.card_image_of_injective Q (Sym2.map.injective hf)

theorem mem_image_edges_iff [DecidableEq W] (f : V → W) (hf : Function.Injective f)
    (Q : Finset (Sym2 V)) (e : Sym2 V) :
    e.map f ∈ Q.image (Sym2.map f) ↔ e ∈ Q := by
  constructor
  · intro he
    obtain ⟨e', he', heq⟩ := Finset.mem_image.mp he
    exact (Sym2.map.injective hf heq) ▸ he'
  · exact Finset.mem_image_of_mem _

theorem image_edges_subset_edgeSet [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    {Q : Finset (Sym2 V)} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) :
    (Q.image (Sym2.map f) : Set (Sym2 W)) ⊆ H.edgeSet := by
  intro e he
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
  exact f.map_mem_edgeSet (hQ he')

theorem endVerts_image [DecidableEq W] (f : V → W) (Q : Finset (Sym2 V)) :
    endVerts (Q.image (Sym2.map f)) = (endVerts Q).image f := by
  ext w
  constructor
  · intro hw
    obtain ⟨e', he', hw⟩ := mem_endVerts.mp hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨x, hx, hfx⟩ := Sym2.mem_map.mp hw
    exact Finset.mem_image.mpr ⟨x, mem_endVerts.mpr ⟨e, he, hx⟩, hfx⟩
  · intro hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨e, he, hxe⟩ := mem_endVerts.mp hx
    exact mem_endVerts.mpr ⟨e.map f, Finset.mem_image_of_mem _ he,
      Sym2.mem_map.mpr ⟨x, hxe, rfl⟩⟩

theorem card_endVerts_image_le [DecidableEq W] (f : V → W) (Q : Finset (Sym2 V)) :
    (endVerts (Q.image (Sym2.map f))).card ≤ (endVerts Q).card := by
  rw [endVerts_image]
  exact Finset.card_image_le

theorem card_endVerts_image [DecidableEq W] (f : V → W) (hf : Function.Injective f)
    (Q : Finset (Sym2 V)) :
    (endVerts (Q.image (Sym2.map f))).card = (endVerts Q).card := by
  rw [endVerts_image, Finset.card_image_of_injective _ hf]

theorem filter_mono_image [DecidableEq W] (f : V → W) (d : W → Bool)
    (Q : Finset (Sym2 V)) :
    (Q.image (Sym2.map f)).filter (mono d) =
      (Q.filter (mono (d ∘ f))).image (Sym2.map f) := by
  simp only [Finset.filter_image, mono_map]

theorem card_filter_mono_image [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (d : W → Bool) (Q : Finset (Sym2 V)) :
    ((Q.image (Sym2.map f)).filter (mono d)).card =
      (Q.filter (mono (d ∘ f))).card := by
  rw [filter_mono_image, card_image_edges f hf]

/-- Universal monochromatic-edge lower bounds transport by composing target colors with `f`. -/
theorem forall_card_filter_mono_image [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) {Q : Finset (Sym2 V)} {k : ℕ}
    (hQ : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    ∀ d : W → Bool, k ≤ ((Q.image (Sym2.map f)).filter (mono d)).card := by
  intro d
  rw [card_filter_mono_image f hf]
  exact hQ (d ∘ f)

/-- The explicit image is an edge certificate with the same size bound. -/
theorem image_certificate [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {Q : Finset (Sym2 V)} {k n : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hcard : Q.card ≤ n)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    (Q.image (Sym2.map f) : Set (Sym2 W)) ⊆ H.edgeSet ∧
      (Q.image (Sym2.map f)).card ≤ n ∧
      ∀ d : W → Bool, k ≤ ((Q.image (Sym2.map f)).filter (mono d)).card := by
  refine ⟨image_edges_subset_edgeSet f hQ, ?_, forall_card_filter_mono_image f hf hmono⟩
  simpa only [card_image_edges f hf] using hcard

theorem embedding_image_certificate [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H)
    {Q : Finset (Sym2 V)} {k n : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hcard : Q.card ≤ n)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    (Q.image (Sym2.map f) : Set (Sym2 W)) ⊆ H.edgeSet ∧
      (Q.image (Sym2.map f)).card ≤ n ∧
      ∀ d : W → Bool, k ≤ ((Q.image (Sym2.map f)).filter (mono d)).card :=
  image_certificate f.toHom f.injective hQ hcard hmono

/- ## Certificates supported on an induced subgraph -/

/-- Extend a Boolean coloring by `false` outside its domain. -/
theorem exists_bool_extension (S : Set V) (c : S → Bool) :
    ∃ d : V → Bool, (∀ v : S, d v = c v) ∧ ∀ v ∉ S, d v = false := by
  classical
  refine ⟨fun v => if h : v ∈ S then c ⟨v, h⟩ else false, ?_, ?_⟩
  · intro v
    simp only [dif_pos v.property]
  · intro v hv
    simp only [dif_neg hv]

/-- All monochromatic certificate edges supported on `S` are bad edges of the induced graph. -/
theorem card_filter_mono_le_badEdges_induce (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (S : Set V) [Finite S] (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet)
    (hS : (endVerts Q : Set V) ⊆ S) (d : V → Bool) :
    (Q.filter (mono d)).card ≤ (badEdges (G.induce S) (fun v : S => d v)).card := by
  classical
  let B := badEdges (G.induce S) (fun v : S => d v)
  have hsub : Q.filter (mono d) ⊆ B.image (Sym2.map (Subtype.val : S → V)) := by
    intro e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨heQ, hec⟩ := Finset.mem_filter.mp he
      have hv : v ∈ S := hS (left_mem_endVerts heQ)
      have hw : w ∈ S := hS (right_mem_endVerts heQ)
      refine Finset.mem_image.mpr ⟨s((⟨v, hv⟩ : S), (⟨w, hw⟩ : S)), ?_, rfl⟩
      exact (mem_badEdges _ _ _ _).mpr
        ⟨hQ heQ, (mono_pair d v w).mp hec⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A universal ambient certificate lower-bounds every coloring of an induced graph containing it. -/
theorem le_badEdges_induce_of_certificate {G : SimpleGraph V} {Q : Finset (Sym2 V)}
    {S : Set V} [Finite S] {k : ℕ} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet)
    (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) (c : S → Bool) :
    k ≤ (badEdges (G.induce S) c).card := by
  obtain ⟨d, hd, _⟩ := exists_bool_extension S c
  have heq : (fun v : S => d v) = c := funext hd
  have hle := card_filter_mono_le_badEdges_induce G Q S hQ hS d
  rw [heq] at hle
  exact (hmono d).trans hle

theorem le_badEdges_induce_finset_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Finset V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : endVerts Q ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    (c : S → Bool) : k ≤ (badEdges (G.induce (S : Set V)) c).card :=
  le_badEdges_induce_of_certificate (S := (S : Set V)) hQ hS hmono c

theorem le_card_bipartite_deletion_induce_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} [Finite S] {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Finset (Sym2 S)} (hbip : ((G.induce S).deleteEdges (E : Set (Sym2 S))).IsBipartite) :
    k ≤ E.card := by
  obtain ⟨c, _, hc⟩ := exists_badEdges_card_le_of_isBipartite_deleteEdges hbip
  exact (le_badEdges_induce_of_certificate hQ hS hmono c).trans hc

/-- Ambient edge deletion cannot bipartize the induced graph using fewer edges than its certificate.
The set `S` and the ambient vertex type need not be finite. -/
theorem le_card_ambient_deletion_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Finset (Sym2 V)} (hbip : ((G.deleteEdges (E : Set (Sym2 V))).induce S).IsBipartite) :
    k ≤ E.card := by
  classical
  obtain ⟨c, hc⟩ := exists_bool_coloring_of_isBipartite hbip
  obtain ⟨d, hd, _⟩ := exists_bool_extension S c
  have hsub : Q.filter (mono d) ⊆ E := by
    intro e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨heQ, hec⟩ := Finset.mem_filter.mp he
      let v' : S := ⟨v, hS (left_mem_endVerts heQ)⟩
      let w' : S := ⟨w, hS (right_mem_endVerts heQ)⟩
      by_contra hnot
      have hadj : ((G.deleteEdges (E : Set (Sym2 V))).induce S).Adj v' w' :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hQ heQ, hnot⟩
      apply hc hadj
      exact (hd v').symm.trans (((mono_pair d v w).mp hec).trans (hd w'))
  exact (hmono d).trans (Finset.card_le_card hsub)

theorem le_ncard_ambient_deletion_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Set (Sym2 V)} (hE : E.Finite) (hbip : ((G.deleteEdges E).induce S).IsBipartite) :
    k ≤ E.ncard := by
  have hbip' : ((G.deleteEdges (hE.toFinset : Set (Sym2 V))).induce S).IsBipartite := by
    simpa only [hE.coe_toFinset] using hbip
  simpa only [Set.ncard_eq_toFinset_card E hE] using
    le_card_ambient_deletion_of_certificate hQ hS hmono hbip'

theorem not_isBipartite_induce_deleteEdges_of_card_lt
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Finset (Sym2 V)} (hE : E.card < k) :
    ¬((G.deleteEdges (E : Set (Sym2 V))).induce S).IsBipartite :=
  fun hbip => (Nat.not_le_of_lt hE) (le_card_ambient_deletion_of_certificate hQ hS hmono hbip)

end Erdos74.Certificates

/-
# Three-color gluing across a four-level annulus

This file is independent of `Submission.Spec`.  Vertices may have any type; no
finiteness or decidable-adjacency assumption is used.

`glue level a γ c c₁` retains `γ` at levels at most `a`, retains the Boolean
coloring `c` (embedded in `Fin 3`) at levels at least `a + 3`, and interpolates
on the two intervening levels.  When `c` and `c₁` differ, the four rows of the
interpolation, listed in the order `(c = false, c = true)`, are
`(1, 0), (2, 0), (2, 1), (0, 1)`.

The core theorem `glue_proper_of_xor` assumes that the XOR of the two Boolean
colorings is constant along edges in the closed band.  `glue_proper` derives
this condition from properness of both Boolean colorings there.
`exists_coloring` packages the result as a mathlib graph coloring, and
`exists_coloring_of_band` accepts the stronger full-band matching hypotheses.

The edge-level hypothesis is the oriented inequality `level u ≤ level v + 1`
for every edge.  By symmetry this is precisely the usual distance-at-most-one
condition; `level_step_of_dist` converts from a `Nat.dist` formulation.
There is no need to assume `1 ≤ a` once the exterior Boolean coloring is
assumed proper on all levels at least `a`.
-/

namespace Erdos74.AnnulusGluing

universe u

variable {V : Type u}

/-- Embed the two Boolean colors as colors `0` and `1` of `Fin 3`. -/
def boolColor : Bool → Fin 3
  | false => 0
  | true => 1

@[simp] theorem boolColor_false : boolColor false = 0 := rfl

@[simp] theorem boolColor_true : boolColor true = 1 := rfl

theorem boolColor_injective : Function.Injective boolColor := by decide

/-- The transition when the two Boolean colorings disagree.
Rows beyond the fourth have already reached the exterior coloring. -/
def swapRow (row : ℕ) (b : Bool) : Fin 3 :=
  if row = 0 then boolColor (!b)
  else if row = 1 then if b then 0 else 2
  else if row = 2 then if b then 1 else 2
  else boolColor b

/-- The color in the closed band: unchanged where the Boolean colorings agree,
and the four-row transition where they disagree. -/
def bandColor (row : ℕ) (b b₁ : Bool) : Fin 3 :=
  if b = b₁ then boolColor b else swapRow row b

@[simp] theorem bandColor_same (row : ℕ) (b : Bool) :
    bandColor row b b = boolColor b := by
  simp [bandColor]

@[simp] theorem bandColor_zero (b b₁ : Bool) :
    bandColor 0 b b₁ = boolColor b₁ := by
  cases b <;> cases b₁ <;> decide

theorem bandColor_of_three_le (row : ℕ) (b b₁ : Bool) (hrow : 3 ≤ row) :
    bandColor row b b₁ = boolColor b := by
  have h0 : row ≠ 0 := by omega
  have h1 : row ≠ 1 := by omega
  have h2 : row ≠ 2 := by omega
  simp [bandColor, swapRow, h0, h1, h2]

@[simp] theorem bandColor_three (b b₁ : Bool) :
    bandColor 3 b b₁ = boolColor b :=
  bandColor_of_three_le 3 b b₁ (by omega)

/-- Two proper Boolean colorings have the same XOR at the endpoints of an edge. -/
theorem xor_eq_of_ne {b d b₁ d₁ : Bool} (h : b ≠ d) (h₁ : b₁ ≠ d₁) :
    Bool.xor b b₁ = Bool.xor d d₁ := by
  cases b <;> cases d <;> cases b₁ <;> cases d₁ <;> simp_all

/-- The finite check behind the gluing argument. -/
private theorem bandColor_ne_finite :
    ∀ (i j : Fin 4) (b b₁ d d₁ : Bool),
      i.val ≤ j.val + 1 → j.val ≤ i.val + 1 →
      b ≠ d → Bool.xor b b₁ = Bool.xor d d₁ →
      bandColor i.val b b₁ ≠ bandColor j.val d d₁ := by
  decide

/-- Neighboring rows give distinct colors whenever the exterior colors differ
and the XOR is unchanged along the edge. -/
theorem bandColor_ne_of_xor {i j : ℕ} {b b₁ d d₁ : Bool}
    (hi : i ≤ 3) (hj : j ≤ 3)
    (hij : i ≤ j + 1) (hji : j ≤ i + 1)
    (h : b ≠ d) (hδ : Bool.xor b b₁ = Bool.xor d d₁) :
    bandColor i b b₁ ≠ bandColor j d d₁ :=
  bandColor_ne_finite ⟨i, by omega⟩ ⟨j, by omega⟩ b b₁ d d₁ hij hji h hδ

/-- A version of the row lemma using properness of both Boolean colorings. -/
theorem bandColor_ne {i j : ℕ} {b b₁ d d₁ : Bool}
    (hi : i ≤ 3) (hj : j ≤ 3)
    (hij : i ≤ j + 1) (hji : j ≤ i + 1)
    (h : b ≠ d) (h₁ : b₁ ≠ d₁) :
    bandColor i b b₁ ≠ bandColor j d d₁ :=
  bandColor_ne_of_xor hi hj hij hji h (xor_eq_of_ne h h₁)

/-- The explicit global coloring.  Its inner and outer agreement properties
hold without any graph-theoretic assumptions. -/
def glue (level : V → ℕ) (a : ℕ) (γ : V → Fin 3) (c c₁ : V → Bool)
    (v : V) : Fin 3 :=
  if level v ≤ a then γ v
  else if a + 3 ≤ level v then boolColor (c v)
  else bandColor (level v - a) (c v) (c₁ v)

variable {G : SimpleGraph V} {level : V → ℕ} {a : ℕ}
  {γ : V → Fin 3} {c c₁ : V → Bool}

theorem glue_eq_inner {v : V} (hv : level v ≤ a) :
    glue level a γ c c₁ v = γ v := by
  simp [glue, hv]

theorem glue_eq_outer {v : V} (hv : a + 3 ≤ level v) :
    glue level a γ c c₁ v = boolColor (c v) := by
  have hinner : ¬ level v ≤ a := by omega
  simp [glue, hinner, hv]

/-- Once the lower boundary matches, the formula for the band also describes
all vertices on or beyond that boundary. -/
theorem glue_eq_band
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v))
    {v : V} (hv : a ≤ level v) :
    glue level a γ c c₁ v = bandColor (level v - a) (c v) (c₁ v) := by
  by_cases hinner : level v ≤ a
  · have heq : level v = a := by omega
    rw [glue_eq_inner hinner, hmatch v heq, heq, Nat.sub_self, bandColor_zero]
  · unfold glue
    rw [if_neg hinner]
    split_ifs with houter
    · exact (bandColor_of_three_le _ _ _ (by omega)).symm
    · rfl

/-- Convert the natural-number absolute-distance bound to the oriented
edge-level hypothesis used below.  The reverse inequality follows by applying
this hypothesis to the reverse edge. -/
theorem level_step_of_dist
    (hlevel : ∀ {u v : V}, G.Adj u v → Nat.dist (level u) (level v) ≤ 1) :
    ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1 := by
  intro u v huv
  have h := hlevel huv
  unfold Nat.dist at h
  omega

/-- Core gluing lemma.  Only the level-`a` boundary needs to match the inner
coloring, and the inner coloring only needs to be proper through level `a`.
The Boolean coloring must be proper on the exterior, including this boundary.
The XOR condition is only needed on edges entirely in the closed four-level
band `[a, a + 3]`. -/
theorem glue_proper_of_xor
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v → level u ≤ a → level v ≤ a → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hδ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      Bool.xor (c u) (c₁ u) = Bool.xor (c v) (c₁ v))
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v)) :
    ∀ {u v : V}, G.Adj u v →
      glue level a γ c c₁ u ≠ glue level a γ c c₁ v := by
  have ordered : ∀ {u v : V}, G.Adj u v → level u ≤ level v →
      glue level a γ c c₁ u ≠ glue level a γ c c₁ v := by
    intro u v huv huv_level
    have hstep := hlevel huv.symm
    by_cases hv : level v ≤ a
    · have hu : level u ≤ a := le_trans huv_level hv
      rw [glue_eq_inner hu, glue_eq_inner hv]
      exact hγ huv hu hv
    by_cases hu : a + 3 ≤ level u
    · have hv : a + 3 ≤ level v := le_trans hu huv_level
      rw [glue_eq_outer hu, glue_eq_outer hv]
      exact boolColor_injective.ne (hc huv (by omega) (by omega))
    have hulo : a ≤ level u := by omega
    have hvlo : a ≤ level v := by omega
    have huhi : level u ≤ a + 3 := by omega
    have hvhi : level v ≤ a + 3 := by omega
    rw [glue_eq_band hmatch hulo, glue_eq_band hmatch hvlo]
    exact bandColor_ne_of_xor (by omega) (by omega) (by omega) (by omega)
      (hc huv hulo hvlo) (hδ huv hulo huhi hvlo hvhi)
  intro u v huv
  rcases le_total (level u) (level v) with h | h
  · exact ordered huv h
  · exact (ordered huv.symm h).symm

/-- Gluing from two proper Boolean colorings.  No separate hypothesis about
XORs or connected components of the band is necessary. -/
theorem glue_proper
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v → level u ≤ a → level v ≤ a → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hc₁ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      c₁ u ≠ c₁ v)
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v)) :
    ∀ {u v : V}, G.Adj u v →
      glue level a γ c c₁ u ≠ glue level a γ c c₁ v := by
  intro u v huv
  apply glue_proper_of_xor hlevel hγ hc ?_ hmatch huv
  intro x y hxy hxlo hxhi hylo hyhi
  exact xor_eq_of_ne (hc hxy hxlo hylo) (hc₁ hxy hxlo hxhi hylo hyhi)

/-- A proper mathlib three-coloring with prescribed inner and outer colors.
This form uses only properness through level `a` and matching at level `a`. -/
theorem exists_coloring
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v → level u ≤ a → level v ≤ a → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hc₁ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      c₁ u ≠ c₁ v)
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v)) :
    ∃ C : G.Coloring (Fin 3),
      (∀ v, level v ≤ a → C v = γ v) ∧
      (∀ v, a + 3 ≤ level v → C v = boolColor (c v)) := by
  let C : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk
    (glue level a γ c c₁) (fun {u v} huv => glue_proper hlevel hγ hc hc₁ hmatch huv)
  refine ⟨C, ?_, ?_⟩
  · intro v hv
    change glue level a γ c c₁ v = γ v
    exact glue_eq_inner hv
  · intro v hv
    change glue level a γ c c₁ v = boolColor (c v)
    exact glue_eq_outer hv

/-- Convenience form with the original full-band hypotheses: `γ` is proper
through level `a + 3` and agrees with the embedded `c₁` throughout the band.
The XOR condition follows automatically, so is not an extra argument. -/
theorem exists_coloring_of_band
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v →
      level u ≤ a + 3 → level v ≤ a + 3 → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hc₁ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      c₁ u ≠ c₁ v)
    (hmatch : ∀ v, a ≤ level v → level v ≤ a + 3 → γ v = boolColor (c₁ v)) :
    ∃ C : G.Coloring (Fin 3),
      (∀ v, level v ≤ a → C v = γ v) ∧
      (∀ v, a + 3 ≤ level v → C v = boolColor (c v)) := by
  apply exists_coloring hlevel ?_ hc hc₁ ?_
  · intro u v huv hu hv
    exact hγ huv (by omega) (by omega)
  · intro v hv
    exact hmatch v (by omega) (by omega)

end Erdos74.AnnulusGluing

/-
# Bounded-walk neighborhoods, capped levels, and empty annuli

`Near G S R v` means that an explicit walk of length at most `R` joins `v` to
one of the finitely many roots in `S`. The natural-number function `level`
is the least such radius, capped at `M`; unreachable vertices are assigned
the cap. No connectedness or finiteness assumption on the vertex type is needed.

The annulus lemma chooses four consecutive levels with a prescribed margin
from every level in a finite exceptional set.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

/-- An explicit walk of length at most `R` from `v` to a root in `S`. -/
def Near (G : SimpleGraph V) (S : Finset V) (R : ℕ) (v : V) : Prop :=
  ∃ s ∈ S, ∃ p : G.Walk v s, p.length ≤ R

variable {G : SimpleGraph V} {S T : Finset V} {M n R R' : ℕ} {v w : V}

/-- Increasing the radius preserves a bounded-walk neighborhood. -/
theorem near_mono (hR : R ≤ R') (hv : Near G S R v) : Near G S R' v := by
  obtain ⟨s, hs, p, hp⟩ := hv
  exact ⟨s, hs, p, hp.trans hR⟩

/-- Adding roots preserves a bounded-walk neighborhood. -/
theorem near_mono_roots (hS : S ⊆ T) (hv : Near G S R v) : Near G T R v := by
  obtain ⟨s, hs, p, hp⟩ := hv
  exact ⟨s, hS hs, p, hp⟩

/-- A root belongs to every nonnegative-radius neighborhood. -/
theorem near_of_mem (hv : v ∈ S) : Near G S R v :=
  ⟨v, hv, .nil, Nat.zero_le R⟩

@[simp] theorem near_zero_iff : Near G S 0 v ↔ v ∈ S := by
  constructor
  · rintro ⟨s, hs, p, hp⟩
    have hvs : v = s := SimpleGraph.Walk.eq_of_length_eq_zero (by omega : p.length = 0)
    simpa only [hvs] using hs
  · exact near_of_mem

/-- Prepending an edge increases the allowed radius by one. -/
theorem near_of_adj (hvw : G.Adj v w) (hw : Near G S R w) :
    Near G S (R + 1) v := by
  obtain ⟨s, hs, p, hp⟩ := hw
  exact ⟨s, hs, .cons hvw p, by simpa using Nat.add_le_add_right hp 1⟩

/-- Prepending a walk increases the allowed radius by its length. -/
theorem near_of_walk (p : G.Walk v w) (hw : Near G S R w) :
    Near G S (R + p.length) v := by
  obtain ⟨s, hs, q, hq⟩ := hw
  refine ⟨s, hs, p.append q, ?_⟩
  simp only [SimpleGraph.Walk.length_append]
  omega

/-- The least bounded-walk radius, capped at `M`. The cap makes this definition
valid even when `S` is empty or `v` is unreachable from `S`. -/
noncomputable def level (G : SimpleGraph V) (S : Finset V) (M : ℕ) (v : V) : ℕ := by
  classical
  exact Nat.find (show ∃ n, Near G S n v ∨ M ≤ n from ⟨M, Or.inr le_rfl⟩)

/-- A level either witnesses a short walk or has reached the cap. -/
theorem level_spec (G : SimpleGraph V) (S : Finset V) (M : ℕ) (v : V) :
    Near G S (level G S M v) v ∨ M ≤ level G S M v := by
  classical
  exact Nat.find_spec (show ∃ n, Near G S n v ∨ M ≤ n from ⟨M, Or.inr le_rfl⟩)

/-- Capped levels never exceed the cap. -/
theorem level_le_cap (G : SimpleGraph V) (S : Finset V) (M : ℕ) (v : V) :
    level G S M v ≤ M := by
  classical
  exact Nat.find_min' _ (Or.inr le_rfl)

/-- Any bounded walk to a root bounds the capped level. -/
theorem level_le_of_near (hv : Near G S n v) : level G S M v ≤ n := by
  classical
  exact Nat.find_min' _ (Or.inl hv)

/-- Every root has level zero, for every cap. -/
@[simp] theorem level_zero_of_mem (hv : v ∈ S) : level G S M v = 0 := by
  exact Nat.eq_zero_of_le_zero (level_le_of_near (near_of_mem (R := 0) hv))

@[simp] theorem level_cap_zero (G : SimpleGraph V) (S : Finset V) (v : V) :
    level G S 0 v = 0 := Nat.eq_zero_of_le_zero (level_le_cap G S 0 v)

/-- Below the cap, the level is witnessed by an actual bounded walk. -/
theorem near_of_level_lt (hv : level G S M v < M) :
    Near G S (level G S M v) v := by
  rcases level_spec G S M v with h | h
  · exact h
  · omega

/-- At any radius strictly below the cap, levels describe exactly `Near`. -/
theorem level_le_iff_near (hn : n < M) : level G S M v ≤ n ↔ Near G S n v := by
  constructor
  · intro hv
    exact near_mono hv (near_of_level_lt (hv.trans_lt hn))
  · exact level_le_of_near

/-- With a positive cap, only roots have level zero. -/
theorem level_zero_iff (hM : 0 < M) : level G S M v = 0 ↔ v ∈ S := by
  rw [← Nat.le_zero, level_le_iff_near hM, near_zero_iff]

/-- Outside the radius-`R` neighborhood, the cap `R + 1` is attained.
This includes vertices in components with no root. -/
theorem level_eq_cap_of_not_near (hv : ¬ Near G S R v) :
    level G S (R + 1) v = R + 1 := by
  have hcap := level_le_cap G S (R + 1) v
  have hnot : ¬ level G S (R + 1) v ≤ R := by
    simpa only [level_le_iff_near (Nat.lt_succ_self R)] using hv
  omega

theorem not_near_iff_level_eq_cap :
    ¬ Near G S R v ↔ level G S (R + 1) v = R + 1 := by
  constructor
  · exact level_eq_cap_of_not_near
  · intro hv hnear
    have := level_le_of_near (M := R + 1) hnear
    omega

/-- Levels increase by at most one across an edge, even at the cap. -/
theorem level_adj_le (hvw : G.Adj v w) :
    level G S M v ≤ level G S M w + 1 := by
  by_cases hw : level G S M w < M
  · exact level_le_of_near (near_of_adj hvw (near_of_level_lt hw))
  · have hv := level_le_cap G S M v
    omega

/-- The symmetric natural-distance version of the edge-level bound. -/
theorem level_adj_dist_le (hvw : G.Adj v w) :
    Nat.dist (level G S M v) (level G S M w) ≤ 1 := by
  have hv := level_adj_le (S := S) (M := M) hvw
  have hw := level_adj_le (S := S) (M := M) hvw.symm
  unfold Nat.dist
  omega

/-- An arbitrary natural-valued edge-1-Lipschitz function changes by at most
the length of a walk. Only the oriented edge inequality is needed. -/
theorem walk_level_ineq {ℓ : V → ℕ}
    (hℓ : ∀ {x y : V}, G.Adj x y → ℓ x ≤ ℓ y + 1)
    (p : G.Walk v w) : ℓ v ≤ ℓ w + p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
      have h := hℓ hxy
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Capped levels change by at most the length of any walk. -/
theorem level_le_add_length (p : G.Walk v w) :
    level G S M v ≤ level G S M w + p.length :=
  walk_level_ineq (fun h => level_adj_le h) p

/- ## A four-level annulus avoiding finitely many exceptional levels -/

/-- Among `k` blocks of length `2 * r + 4`, fewer than `k` exceptional vertices
leave one block unused. Its central four levels are at distance greater than
`r` from all exceptional levels.

The image of `(ℓ z - 1) / (2 * r + 4)` has at most `Z.card` elements. Level zero
may mark block zero unnecessarily, and large levels may mark blocks outside
the range, but neither affects the cardinality argument. -/
theorem exists_separated_annulus_of_card_lt
    (Z : Finset V) (ℓ : V → ℕ) (k r : ℕ) (hcard : Z.card < k) :
    ∃ a : ℕ, 1 ≤ a ∧ a + 3 ≤ k * (2 * r + 4) ∧
      ∀ z ∈ Z, ∀ l : ℕ, a ≤ l → l ≤ a + 3 →
        ℓ z + r < l ∨ l + r < ℓ z := by
  classical
  let L := 2 * r + 4
  let occupied := Z.image (fun z => (ℓ z - 1) / L)
  have hoccupied : occupied.card < (Finset.range k).card := by
    simpa only [Finset.card_range] using
      (Finset.card_image_le (s := Z) (f := fun z => (ℓ z - 1) / L)).trans_lt hcard
  obtain ⟨i, hi, hi_unused⟩ := Finset.exists_mem_notMem_of_card_lt_card hoccupied
  have hik : i < k := Finset.mem_range.mp hi
  have hnext : i * L + L ≤ k * L := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right L (by omega : i + 1 ≤ k)
  have hL : L = 2 * r + 4 := rfl
  refine ⟨i * L + 1 + r, by omega, ?_, ?_⟩
  · change i * L + 1 + r + 3 ≤ k * L
    omega
  · intro z hz l hlo hhi
    by_contra hsep
    simp only [not_or, not_lt] at hsep
    apply hi_unused
    apply Finset.mem_image.mpr
    refine ⟨z, hz, Nat.div_eq_of_lt_le ?_ ?_⟩
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The annulus bound used by the localized three-color induction: if
`Z.card ≤ 2 * t - 2` and `t > 0`, there are four consecutive levels in
`1, ..., (2 * t - 1) * (2 * r + 4)` separated from every exceptional level by
more than `r`. This applies to arbitrary natural-valued levels. -/
theorem exists_separated_annulus
    (Z : Finset V) (ℓ : V → ℕ) {t r : ℕ}
    (ht : 0 < t) (hcard : Z.card ≤ 2 * t - 2) :
    ∃ a : ℕ, 1 ≤ a ∧ a + 3 ≤ (2 * t - 1) * (2 * r + 4) ∧
      ∀ z ∈ Z, ∀ l : ℕ, a ≤ l → l ≤ a + 3 →
        ℓ z + r < l ∨ l + r < ℓ z := by
  exact exists_separated_annulus_of_card_lt Z ℓ (2 * t - 1) r (by omega)

/-- The same annulus lemma with membership in the closed finite interval. -/
theorem exists_separated_annulus_Icc
    (Z : Finset V) (ℓ : V → ℕ) {t r : ℕ}
    (ht : 0 < t) (hcard : Z.card ≤ 2 * t - 2) :
    ∃ a : ℕ, 1 ≤ a ∧ a + 3 ≤ (2 * t - 1) * (2 * r + 4) ∧
      ∀ z ∈ Z, ∀ l ∈ Finset.Icc a (a + 3),
        ℓ z + r < l ∨ l + r < ℓ z := by
  obtain ⟨a, ha, hbound, hsep⟩ := exists_separated_annulus Z ℓ (r := r) ht hcard
  exact ⟨a, ha, hbound, fun z hz l hl =>
    hsep z hz l (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2⟩

end Erdos74.Certificates

/-
# Short walk covers after deleting finitely many edges

Truncating a walk just before its first deleted edge preserves its length bound.
Thus a short-walk cover by `S` becomes a cover by `S ∪ endVerts A` after deleting
`A`. In particular, a cover by the endpoints of the deleted edges is preserved.
No finiteness assumption on the vertex type or spanning forest is needed.

The level-ball lemmas show that a short walk to level zero stays in a level
ball, and restrict it to the corresponding induced subgraph without changing
its length.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

/-- Stop just before the first edge of `A`, or keep the whole walk if it avoids
`A`. The resulting walk ends in `S ∪ endVerts A` and is no longer than `p`. -/
theorem walk_truncate_deleteEdges [DecidableEq V]
    {B : SimpleGraph V} (S : Finset V) (A : Finset (Sym2 V))
    {v s : V} (hs : s ∈ S) (p : B.Walk v s) :
    ∃ r ∈ S ∪ endVerts A,
      ∃ q : (B.deleteEdges (A : Set (Sym2 V))).Walk v r, q.length ≤ p.length := by
  classical
  induction p with
  | @nil s =>
      exact ⟨s, Finset.mem_union_left _ hs, .nil, le_rfl⟩
  | @cons v w s hvw p ih =>
      by_cases hA : s(v, w) ∈ A
      · exact ⟨v, Finset.mem_union_right _ (left_mem_endVerts hA), .nil,
          Nat.zero_le _⟩
      · obtain ⟨r, hr, q, hq⟩ := ih hs
        refine ⟨r, hr, .cons (SimpleGraph.deleteEdges_adj.mpr ⟨hvw, hA⟩) q, ?_⟩
        simpa only [SimpleGraph.Walk.length_cons] using Nat.add_le_add_right hq 1

/-- Deleting `A` preserves a radius bound if its endpoints are added to the
set of roots. This requires neither connectedness nor a finite vertex type. -/
theorem radius_after_deletion [DecidableEq V]
    {B : SimpleGraph V} (S : Finset V) (A : Finset (Sym2 V)) {R : ℕ}
    (hcover : ∀ v, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R) :
    ∀ v, ∃ r ∈ S ∪ endVerts A,
      ∃ q : (B.deleteEdges (A : Set (Sym2 V))).Walk v r, q.length ≤ R := by
  intro v
  obtain ⟨s, hs, p, hp⟩ := hcover v
  obtain ⟨r, hr, q, hq⟩ := walk_truncate_deleteEdges S A hs p
  exact ⟨r, hr, q, hq.trans hp⟩

/-- A walk to an endpoint of `F` can be truncated to a walk in `G.deleteEdges F`
to an endpoint of `F`, without increasing its length. -/
theorem walk_to_endVerts_after_deletion
    {G : SimpleGraph V} (F : Finset (Sym2 V)) {v s : V}
    (hs : s ∈ endVerts F) (p : G.Walk v s) :
    ∃ r ∈ endVerts F,
      ∃ q : (G.deleteEdges (F : Set (Sym2 V))).Walk v r, q.length ≤ p.length := by
  classical
  simpa only [Finset.union_self] using walk_truncate_deleteEdges (endVerts F) F hs p

/-- A short-walk cover by `endVerts F` remains such a cover after deleting `F`. -/
theorem radius_endVerts_after_deletion
    {G : SimpleGraph V} (F : Finset (Sym2 V)) {R : ℕ}
    (hcover : ∀ v, ∃ s ∈ endVerts F, ∃ p : G.Walk v s, p.length ≤ R) :
    ∀ v, ∃ r ∈ endVerts F,
      ∃ q : (G.deleteEdges (F : Set (Sym2 V))).Walk v r, q.length ≤ R := by
  classical
  simpa only [Finset.union_self] using radius_after_deletion (endVerts F) F hcover

/- ## Restricting short walks to level balls -/

/-- If levels rise by at most one across an edge, every vertex of a walk has
level at most the terminal level plus the length of the walk. The oriented
edge inequality suffices, since adjacency is symmetric. -/
theorem level_le_add_length_of_mem_support
    {G : SimpleGraph V} {ℓ : V → ℕ}
    (hℓ : ∀ {x y : V}, G.Adj x y → ℓ x ≤ ℓ y + 1)
    {v root : V} (p : G.Walk v root) {x : V} (hx : x ∈ p.support) :
    ℓ x ≤ ℓ root + p.length := by
  induction p generalizing x with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      simp
  | @cons v w root hvw p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      simp only [SimpleGraph.Walk.length_cons]
      rcases hx with rfl | hx
      · have hw := ih p.start_mem_support
        have hv := hℓ hvw
        omega
      · exact (ih hx).trans (by omega)

/-- Every vertex of a walk ending at level zero has level at most its length. -/
theorem level_le_length_of_mem_support
    {G : SimpleGraph V} {ℓ : V → ℕ}
    (hℓ : ∀ {x y : V}, G.Adj x y → ℓ x ≤ ℓ y + 1)
    {v root : V} (hroot : ℓ root = 0) (p : G.Walk v root)
    {x : V} (hx : x ∈ p.support) : ℓ x ≤ p.length := by
  simpa only [hroot, Nat.zero_add] using level_le_add_length_of_mem_support hℓ p hx

/-- A walk of length at most `R` to level zero lies entirely in the level-`R` ball. -/
theorem walk_support_in_level_ball
    {G : SimpleGraph V} {ℓ : V → ℕ}
    (hℓ : ∀ {x y : V}, G.Adj x y → ℓ x ≤ ℓ y + 1)
    {v root : V} (hroot : ℓ root = 0) (p : G.Walk v root)
    {R : ℕ} (hp : p.length ≤ R) :
    ∀ x ∈ p.support, x ∈ {x : V | ℓ x ≤ R} := by
  intro x hx
  exact (level_le_length_of_mem_support hℓ hroot p hx).trans hp

/-- Restricting a walk to an induced subgraph does not change its length. -/
@[simp] theorem walk_induce_length
    {G : SimpleGraph V} {T : Set V} {v w : V} (p : G.Walk v w)
    (hp : ∀ x ∈ p.support, x ∈ T) : (p.induce T hp).length = p.length := by
  simpa only [SimpleGraph.Walk.length_map] using
    congrArg SimpleGraph.Walk.length (p.map_induce hp)

/-- Restrict a walk whose support lies in `T` to `G.induce T`, retaining the
original length. Endpoint membership proofs are immaterial. -/
theorem exists_induced_walk_of_support_subset
    {G : SimpleGraph V} {T : Set V} {v w : T} (p : G.Walk (v : V) (w : V))
    (hp : ∀ x ∈ p.support, x ∈ T) :
    ∃ q : (G.induce T).Walk v w, q.length = p.length := by
  exact ⟨p.induce T hp, walk_induce_length p hp⟩

/-- A short walk to level zero restricts to the induced level ball without
changing its length. This is stated for endpoints already in the ball. -/
theorem exists_induced_walk_of_level_zero
    {G : SimpleGraph V} {ℓ : V → ℕ}
    (hℓ : ∀ {x y : V}, G.Adj x y → ℓ x ≤ ℓ y + 1)
    {R : ℕ} {v root : {x : V // ℓ x ≤ R}}
    (hroot : ℓ (root : V) = 0) (p : G.Walk (v : V) (root : V))
    (hp : p.length ≤ R) :
    ∃ q : (G.induce {x : V | ℓ x ≤ R}).Walk v root, q.length = p.length := by
  exact exists_induced_walk_of_support_subset p (walk_support_in_level_ball hℓ hroot p hp)

end Erdos74.Certificates

/-
# Compressing a bounded walk cover to representative edge constraints

Let `P ≤ D`, let `c` properly Boolean-color `P`, and assign every vertex a walk
in `P` of length at most `R` to a root in a finite set `K`. For each ordered pair
of signatures `(root v, c v)`, choose one realizing edge of `D`, if there is one.
Keep this edge and the two walks from its endpoints to their roots.

The resulting finite set has at most `(2 * R + 1) * (2 * K.card) ^ 2` edges.
Any proper Boolean coloring of it yields, by rootwise color flips, a proper
coloring of `D`. In particular, if `D` is not bipartite, every Boolean
coloring has a monochromatic edge in this bounded finite set.

No finiteness, nonemptiness, or decidable-adjacency assumption on `V` is used.
Unrealized signature pairs contribute the empty set. All retained edges lie
in `D.edgeSet`, so in particular none is a loop.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

private theorem xor_eq_of_both_ne {a b x y : Bool} (hab : a ≠ b) (hxy : x ≠ y) :
    Bool.xor a x = Bool.xor b y := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all

/-- The XOR of two proper Boolean colorings is constant along a walk.
The second coloring need only be proper on the edges of this walk. -/
theorem walk_xor_eq_of_proper
    {P : SimpleGraph V} (c d : V → Bool)
    (hc : ∀ ⦃v w : V⦄, P.Adj v w → c v ≠ c w)
    {v w : V} (p : P.Walk v w)
    (hd : ∀ e ∈ p.edges, ¬mono d e) :
    Bool.xor (d v) (c v) = Bool.xor (d w) (c w) := by
  induction p with
  | nil => rfl
  | @cons v w z hvw p ih =>
      have hdvw : d v ≠ d w := by
        simpa only [mono_pair] using hd s(v, w) (by simp)
      apply (xor_eq_of_both_ne hdvw (hc hvw)).trans
      apply ih
      intro e he
      apply hd e
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inr he

/-- A bounded walk cover of a properly Boolean-colored spanning subgraph
compresses all bipartiteness constraints to a uniformly bounded finite edge set.
The bound depends only on the walk radius and the number of roots. -/
theorem exists_representative_constraints
    {P D : SimpleGraph V} (hPD : P ≤ D)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, P.Adj v w → c v ≠ c w)
    (K : Finset V) (root : V → K)
    (p : ∀ v : V, P.Walk v (root v).val) {R : ℕ}
    (hp : ∀ v, (p v).length ≤ R) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ D.edgeSet ∧
      Q.card ≤ (2 * R + 1) * (2 * K.card) ^ 2 ∧
      ∀ d : V → Bool, (∀ e ∈ Q, ¬mono d e) → D.IsBipartite := by
  classical
  let sig : V → K × Bool := fun v => (root v, c v)
  let color : (V → Bool) → K × Bool → Bool := fun d s =>
    Bool.xor (Bool.xor (d s.1.val) (c s.1.val)) s.2
  let realized : ((K × Bool) × (K × Bool)) → Prop := fun i =>
    ∃ v w : V, D.Adj v w ∧ sig v = i.1 ∧ sig w = i.2
  have hcolor (d : V → Bool) (v : V)
      (hd : ∀ e ∈ (p v).edges, ¬mono d e) : color d (sig v) = d v := by
    change Bool.xor (Bool.xor (d (root v).val) (c (root v).val)) (c v) = d v
    rw [← walk_xor_eq_of_proper c d hc (p v) hd,
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  have hwalk_sub (v : V) :
      ((p v).edges.toFinset : Set (Sym2 V)) ⊆ D.edgeSet := by
    intro e he
    exact SimpleGraph.edgeSet_mono hPD
      ((p v).edges_subset_edgeSet (List.mem_toFinset.mp he))
  have hwalk_card (v : V) : (p v).edges.toFinset.card ≤ R := by
    calc
      (p v).edges.toFinset.card ≤ (p v).edges.length := List.toFinset_card_le _
      _ = (p v).length := (p v).length_edges
      _ ≤ R := hp v
  have hpieces : ∀ i : (K × Bool) × (K × Bool),
      ∃ F : Finset (Sym2 V), (F : Set (Sym2 V)) ⊆ D.edgeSet ∧
        F.card ≤ 2 * R + 1 ∧
        ∀ d : V → Bool, (∀ e ∈ F, ¬mono d e) →
          realized i → color d i.1 ≠ color d i.2 := by
    intro i
    by_cases hi : realized i
    · obtain ⟨v, w, hvw, hv, hw⟩ := hi
      refine ⟨insert s(v, w) ((p v).edges.toFinset ∪ (p w).edges.toFinset),
        ?_, ?_, ?_⟩
      · intro e he
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_union] at he
        rcases he with rfl | he | he
        · exact hvw
        · exact hwalk_sub v he
        · exact hwalk_sub w he
      · calc
          _ ≤ ((p v).edges.toFinset ∪ (p w).edges.toFinset).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ (p v).edges.toFinset.card + (p w).edges.toFinset.card + 1 :=
            Nat.add_le_add_right (Finset.card_union_le _ _) 1
          _ ≤ 2 * R + 1 := by
            have hvcard := hwalk_card v
            have hwcard := hwalk_card w
            omega
      · intro d hd _
        have hcv : color d i.1 = d v := by
          rw [← hv]
          apply hcolor
          intro e he
          exact hd e (Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (List.mem_toFinset.mpr he)))
        have hcw : color d i.2 = d w := by
          rw [← hw]
          apply hcolor
          intro e he
          exact hd e (Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (List.mem_toFinset.mpr he)))
        rw [hcv, hcw]
        simpa only [mono_pair] using hd s(v, w) (Finset.mem_insert_self _ _)
    · exact ⟨∅, by simp, by simp, fun _ _ h => (hi h).elim⟩
  choose piece hpiece_sub hpiece_card hpiece_color using hpieces
  let Q : Finset (Sym2 V) := Finset.univ.biUnion piece
  have hpiece_mem (i : (K × Bool) × (K × Bool)) : piece i ⊆ Q :=
    Finset.subset_biUnion_of_mem piece (Finset.mem_univ i)
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
    exact hpiece_sub i hei
  · calc
      Q.card ≤ (Finset.univ : Finset ((K × Bool) × (K × Bool))).card * (2 * R + 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun i _ => hpiece_card i)
      _ = (2 * R + 1) * (2 * K.card) ^ 2 := by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
          Fintype.card_bool]
        ring
  · intro d hd
    apply isBipartite_of_bool_coloring (fun v => color d (sig v))
    intro v w hvw
    exact hpiece_color (sig v, sig w) d
      (fun e he => hd e (hpiece_mem _ he)) ⟨v, w, hvw, rfl, rfl⟩

/-- Direct certificate form: if `D` is not bipartite, every Boolean coloring
has a monochromatic edge in the representative edge set. No coloring structure
or proper-coloring predicate is needed in the conclusion. -/
theorem exists_representative_constraints_of_not_isBipartite
    {P D : SimpleGraph V} (hPD : P ≤ D)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, P.Adj v w → c v ≠ c w)
    (K : Finset V) (root : V → K)
    (p : ∀ v : V, P.Walk v (root v).val) {R : ℕ}
    (hp : ∀ v, (p v).length ≤ R) (hD : ¬D.IsBipartite) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ D.edgeSet ∧
      Q.card ≤ (2 * R + 1) * (2 * K.card) ^ 2 ∧
      ∀ d : V → Bool, ∃ e ∈ Q, mono d e := by
  classical
  obtain ⟨Q, hQD, hQcard, hQproper⟩ :=
    exists_representative_constraints hPD c hc K root p hp
  refine ⟨Q, hQD, hQcard, ?_⟩
  intro d
  by_contra hbad
  apply hD (hQproper d ?_)
  intro e he hmono
  exact hbad ⟨e, he, hmono⟩

/-- Version accepting an existential bounded walk cover, without preselecting
roots or walks. -/
theorem exists_representative_constraints_of_walk_cover
    {P D : SimpleGraph V} (hPD : P ≤ D)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, P.Adj v w → c v ≠ c w)
    (K : Finset V) {R : ℕ}
    (hcover : ∀ v : V, ∃ r ∈ K, ∃ p : P.Walk v r, p.length ≤ R) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ D.edgeSet ∧
      Q.card ≤ (2 * R + 1) * (2 * K.card) ^ 2 ∧
      ∀ d : V → Bool, (∀ e ∈ Q, ¬mono d e) → D.IsBipartite := by
  classical
  choose root hroot p hp using hcover
  exact exists_representative_constraints hPD c hc K
    (fun v => ⟨root v, hroot v⟩) p hp

/-- An existential bounded walk cover yields a bounded edge set hitting the
monochromatic edges of every Boolean coloring of a non-bipartite graph. -/
theorem exists_representative_certificate_of_walk_cover
    {P D : SimpleGraph V} (hPD : P ≤ D)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, P.Adj v w → c v ≠ c w)
    (K : Finset V) {R : ℕ}
    (hcover : ∀ v : V, ∃ r ∈ K, ∃ p : P.Walk v r, p.length ≤ R)
    (hD : ¬D.IsBipartite) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ D.edgeSet ∧
      Q.card ≤ (2 * R + 1) * (2 * K.card) ^ 2 ∧
      ∀ d : V → Bool, ∃ e ∈ Q, mono d e := by
  classical
  choose root hroot p hp using hcover
  exact exists_representative_constraints_of_not_isBipartite hPD c hc K
    (fun v => ⟨root v, hroot v⟩) p hp hD

end Erdos74.Certificates

/-
# A generic finite branching certificate

An oracle supplies a uniformly bounded finite set, disjoint from any set of fewer
than `t` previously chosen elements, that hits every predicate `bad d`. Branching
on all oracle elements produces one finite set containing at least `t` bad
elements for every `d`.

There are no graph-theoretic or finiteness assumptions on the types involved.
The existence theorems accept arbitrary predicate deciders, which are available
for every `bad` using `classical`; no decidable-equality instance is required.
-/

namespace Erdos74.Certificates

universe u v

/-- A bound for a branching tree with `k` remaining levels. -/
def branchSize (t b : ℕ) : ℕ → ℕ
  | 0 => t
  | k + 1 => t + b * branchSize t b k

@[simp] theorem branchSize_zero (t b : ℕ) : branchSize t b 0 = t := rfl

@[simp] theorem branchSize_succ (t b k : ℕ) :
    branchSize t b (k + 1) = t + b * branchSize t b k := rfl

variable {E : Type u} {C : Type v}

/-- The branching invariant: starting from `A` with `A.card + k = t`, extend `A`
to a bounded finite subset of `U`. Every predicate that holds on all of `A`
holds on at least `t` elements of the extension. -/
theorem exists_branching_extension
    (bad : C → E → Prop) [∀ d, DecidablePred (bad d)] (U : Set E) (t b : ℕ)
    (horacle : ∀ A : Finset E, A.card < t → (A : Set E) ⊆ U →
      ∃ Q : Finset E, (Q : Set E) ⊆ U ∧ Disjoint Q A ∧ Q.card ≤ b ∧
        ∀ d : C, ∃ e ∈ Q, bad d e)
    (k : ℕ) (A : Finset E) (hA : (A : Set E) ⊆ U)
    (hcard : A.card + k = t) :
    ∃ J : Finset E, A ⊆ J ∧ (J : Set E) ⊆ U ∧
      J.card ≤ branchSize t b k ∧
      ∀ d : C, (∀ e ∈ A, bad d e) → t ≤ (J.filter (bad d)).card := by
  classical
  induction k generalizing A with
  | zero =>
      refine ⟨A, Finset.Subset.refl A, hA, ?_, ?_⟩
      · simpa only [branchSize_zero, Nat.add_zero] using hcard.le
      · intro d hbad
        rw [Finset.filter_eq_self.mpr hbad]
        omega
  | succ k ih =>
      have hlt : A.card < t := by omega
      obtain ⟨Q, hQU, hQA, hQb, hhit⟩ := horacle A hlt hA
      have hchildren : ∀ e ∈ Q, ∃ J : Finset E,
          insert e A ⊆ J ∧ (J : Set E) ⊆ U ∧
            J.card ≤ branchSize t b k ∧
            ∀ d : C, (∀ x ∈ insert e A, bad d x) →
              t ≤ (J.filter (bad d)).card := by
        intro e he
        apply ih (insert e A)
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hQU he
          · exact hA hx
        · rw [Finset.card_insert_of_notMem (Finset.disjoint_left.mp hQA he)]
          omega
      choose! child _ hchildU hchildCard hchildBad using hchildren
      let J : Finset E := A ∪ Q.biUnion child
      have hchildSubset (e : E) (he : e ∈ Q) : child e ⊆ J :=
        (Finset.subset_biUnion_of_mem child he).trans Finset.subset_union_right
      refine ⟨J, Finset.subset_union_left, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hA hx
        · obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
          exact hchildU e he hx
      · calc
          J.card ≤ A.card + (Q.biUnion child).card := Finset.card_union_le _ _
          _ ≤ t + b * branchSize t b k :=
            Nat.add_le_add (Nat.le_of_lt hlt)
              ((Finset.card_biUnion_le_card_mul Q child _ hchildCard).trans
                (Nat.mul_le_mul_right _ hQb))
          _ = branchSize t b (k + 1) := rfl
      · intro d hbadA
        obtain ⟨e, he, hbadE⟩ := hhit d
        have hbadInsert : ∀ x ∈ insert e A, bad d x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hbadE
          · exact hbadA x hx
        exact (hchildBad e he d hbadInsert).trans
          (Finset.card_le_card
            (Finset.filter_subset_filter (bad d) (hchildSubset e he)))

/-- A uniformly bounded disjoint hitting-set oracle yields a single finite
subset of `U` with at least `t` bad elements for every `d`. The bound depends
only on `t` and `b`, not on either type or on the oracle. -/
theorem exists_branching_certificate
    (bad : C → E → Prop) [∀ d, DecidablePred (bad d)] (U : Set E) (t b : ℕ)
    (horacle : ∀ A : Finset E, A.card < t → (A : Set E) ⊆ U →
      ∃ Q : Finset E, (Q : Set E) ⊆ U ∧ Disjoint Q A ∧ Q.card ≤ b ∧
        ∀ d : C, ∃ e ∈ Q, bad d e) :
    ∃ J : Finset E, (J : Set E) ⊆ U ∧ J.card ≤ branchSize t b t ∧
      ∀ d : C, t ≤ (J.filter (bad d)).card := by
  classical
  obtain ⟨J, _, hJU, hJcard, hJbad⟩ :=
    exists_branching_extension bad U t b horacle t ∅ (by simp) (by simp)
  exact ⟨J, hJU, hJcard, fun d => hJbad d (by simp)⟩

end Erdos74.Certificates

/-
# Edge certificates from a bounded-radius walk cover

Suppose `B ≤ H`, a Boolean coloring is proper on `B`, and every vertex has a
walk in `B` of length at most `R` to one of at most `2 * t` roots. If deleting
fewer than `t` edges never makes `H` bipartite, there is a finite edge set of
size at most `radiusCertificateBound t R` containing at least `t`
monochromatic edges for every Boolean coloring.

After deleting a fault set `A`, add its endpoints to the roots. There are at
most `4 * t` resulting roots. Representative constraints give an oracle of
size at most `radiusOracleBound t R`, disjoint from `A`; finite branching
then gives the certificate. Neither the vertex type nor the graph needs to
be finite, and `t = 0` is allowed.
-/

namespace Erdos74.Certificates

/-- The maximum size of one representative certificate after fewer than `t`
faults, starting with at most `2 * t` roots and walk radius `R`. -/
def radiusOracleBound (t R : ℕ) : ℕ := (2 * R + 1) * (8 * t) ^ 2

/-- The size bound for the depth-`t` branching certificate built from the
bounded-radius oracle. -/
def radiusCertificateBound (t R : ℕ) : ℕ :=
  branchSize t (radiusOracleBound t R) t

@[simp] theorem radiusOracleBound_zero (R : ℕ) : radiusOracleBound 0 R = 0 := by
  simp [radiusOracleBound]

@[simp] theorem radiusCertificateBound_zero (R : ℕ) :
    radiusCertificateBound 0 R = 0 := rfl

universe u
variable {V : Type u}

/-- The bounded-radius oracle. A non-bipartite deletion has a uniformly bounded
finite edge certificate disjoint from the fault set `A`. The faults need not
be edges of `H`, and no finiteness assumption on `V` is required. -/
theorem exists_radius_oracle
    {B H : SimpleGraph V} (hBH : B ≤ H)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, B.Adj v w → c v ≠ c w)
    (S : Finset V) {t R : ℕ} (hS : S.card ≤ 2 * t)
    (hcover : ∀ v : V, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R)
    (A : Finset (Sym2 V)) (hA : A.card < t)
    (hfarA : ¬(H.deleteEdges (A : Set (Sym2 V))).IsBipartite) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ H.edgeSet ∧
      Disjoint Q A ∧ Q.card ≤ radiusOracleBound t R ∧
      ∀ d : V → Bool, ∃ e ∈ Q, mono d e := by
  classical
  let K : Finset V := S ∪ endVerts A
  have hKcard : K.card ≤ 4 * t := by
    calc
      K.card ≤ S.card + (endVerts A).card := Finset.card_union_le _ _
      _ ≤ 2 * t + 2 * A.card := Nat.add_le_add hS (card_endVerts_le A)
      _ ≤ 4 * t := by omega
  have hPD : B.deleteEdges (A : Set (Sym2 V)) ≤
      H.deleteEdges (A : Set (Sym2 V)) := SimpleGraph.deleteEdges_mono hBH
  have hcP : ∀ ⦃v w : V⦄,
      (B.deleteEdges (A : Set (Sym2 V))).Adj v w → c v ≠ c w :=
    fun _ _ h => hc (SimpleGraph.deleteEdges_adj.mp h).1
  have hcoverP : ∀ v : V, ∃ r ∈ K,
      ∃ p : (B.deleteEdges (A : Set (Sym2 V))).Walk v r, p.length ≤ R :=
    radius_after_deletion S A hcover
  obtain ⟨Q, hQD, hQcard, hQbad⟩ :=
    exists_representative_certificate_of_walk_cover hPD c hcP K hcoverP hfarA
  have hQdiff : (Q : Set (Sym2 V)) ⊆ H.edgeSet \ (A : Set (Sym2 V)) := by
    simpa only [SimpleGraph.edgeSet_deleteEdges] using hQD
  refine ⟨Q, fun _ he => (hQdiff he).1, ?_, ?_, hQbad⟩
  · exact Finset.disjoint_left.mpr (fun _ heQ heA => (hQdiff heQ).2 heA)
  · apply hQcard.trans
    have hroots : 2 * K.card ≤ 8 * t := by omega
    unfold radiusOracleBound
    simpa only [pow_two] using
      Nat.mul_le_mul_left (2 * R + 1) (Nat.mul_le_mul hroots hroots)

/-- A bounded walk cover of a properly Boolean-colored subgraph gives a finite
certificate with at least `t` monochromatic edges for every Boolean coloring,
provided every deletion of fewer than `t` edges leaves `H` non-bipartite.
This is the generic graph-pair theorem: it uses neither finiteness of `V`,
positivity of `t`, nor a minimum bipartizing deletion. -/
theorem exists_radius_certificate
    {B H : SimpleGraph V} (hBH : B ≤ H)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, B.Adj v w → c v ≠ c w)
    (S : Finset V) {t R : ℕ} (hS : S.card ≤ 2 * t)
    (hcover : ∀ v : V, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R)
    (hfar : ∀ A : Finset (Sym2 V), A.card < t →
      ¬(H.deleteEdges (A : Set (Sym2 V))).IsBipartite) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ H.edgeSet ∧
      Q.card ≤ radiusCertificateBound t R ∧
      ∀ d : V → Bool, t ≤ (Q.filter (mono d)).card := by
  exact exists_branching_certificate mono H.edgeSet t (radiusOracleBound t R)
    (fun A hA _ => exists_radius_oracle hBH c hc S hS hcover A hA (hfar A hA))

/-- Finite-vertex specialization: it suffices that every Boolean coloring of
`H` has at least `t` bad edges. Only this specialization needs `[Finite V]`. -/
theorem exists_radius_certificate_of_badEdges [Finite V]
    {B H : SimpleGraph V} (hBH : B ≤ H)
    (c : V → Bool) (hc : ∀ ⦃v w : V⦄, B.Adj v w → c v ≠ c w)
    (S : Finset V) {t R : ℕ} (hS : S.card ≤ 2 * t)
    (hcover : ∀ v : V, ∃ s ∈ S, ∃ p : B.Walk v s, p.length ≤ R)
    (hfar : ∀ d : V → Bool, t ≤ (badEdges H d).card) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ H.edgeSet ∧
      Q.card ≤ radiusCertificateBound t R ∧
      ∀ d : V → Bool, t ≤ (Q.filter (mono d)).card := by
  apply exists_radius_certificate hBH c hc S hS hcover
  intro A hA hbip
  obtain ⟨d, _, hd⟩ := exists_badEdges_card_le_of_isBipartite_deleteEdges hbip
  exact (Nat.not_le_of_lt hA) ((hfar d).trans hd)

end Erdos74.Certificates

/-
# Certificates from a ball around the bad-edge endpoints

The radius-`R` ball around the endpoints of the bad edges of a Boolean coloring
has a properly colored spanning subgraph with a radius-`R` walk cover by at most
`2 * t` roots. If every Boolean coloring of the induced ball has at least `t`
bad edges, the radius certificate therefore gives an ambient edge certificate.

The ball is expanded in the public hypothesis; no auxiliary vertex-set
definition or positivity assumption on `t` or `R` is required.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

/-- If the radius-`R` ball around the endpoints of the `t` bad edges of `c`
still has at least `t` bad edges under every Boolean coloring, then `G` has an
ambient certificate of size at most `radiusCertificateBound t R` forcing at
least `t` monochromatic edges under every Boolean coloring. The cap `R + 1`
ensures that the ball consists exactly of vertices with a walk of length at
most `R` to a bad-edge endpoint. -/
theorem exists_ball_certificate_of_badEdges [Finite V]
    (G : SimpleGraph V) (c : V → Bool) {t R : ℕ}
    (hcard : (badEdges G c).card = t)
    (hfar : ∀ d : {v : V // level G (endVerts (badEdges G c)) (R + 1) v ≤ R} → Bool,
      t ≤ (badEdges
        (G.induce {v : V | level G (endVerts (badEdges G c)) (R + 1) v ≤ R}) d).card) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧
      Q.card ≤ radiusCertificateBound t R ∧
      ∀ d : V → Bool, t ≤ (Q.filter (mono d)).card := by
  classical
  let F := badEdges G c
  let S := endVerts F
  let ℓ := level G S (R + 1)
  let T : Set V := {v | ℓ v ≤ R}
  let H := G.induce T
  let B := (G.deleteEdges (F : Set (Sym2 V))).induce T
  have hBH : B ≤ H := fun _ _ h => (SimpleGraph.deleteEdges_adj.mp h).1
  let c0 : T → Bool := fun v => c v
  have hc : ∀ ⦃v w : T⦄, B.Adj v w → c0 v ≠ c0 w :=
    fun _ _ h => proper_delete_badEdges G c h
  let f : S → T := fun s => ⟨s.val, by
    change level G S (R + 1) s.val ≤ R
    rw [level_zero_of_mem s.property]
    exact Nat.zero_le R⟩
  let S_H : Finset T := S.attach.image f
  have hScard : S_H.card ≤ 2 * t := by
    calc
      S_H.card ≤ S.attach.card := Finset.card_image_le
      _ = S.card := Finset.card_attach
      _ ≤ 2 * F.card := card_endVerts_le F
      _ = 2 * t := by rw [show F.card = t from hcard]
  have hℓ : ∀ {x y : V}, (G.deleteEdges (F : Set (Sym2 V))).Adj x y →
      ℓ x ≤ ℓ y + 1 :=
    fun h => level_adj_le (SimpleGraph.deleteEdges_adj.mp h).1
  have hcover : ∀ v : T, ∃ s ∈ S_H, ∃ p : B.Walk v s, p.length ≤ R := by
    intro v
    have hv : level G S (R + 1) (v : V) ≤ R := v.property
    obtain ⟨s, hs, p, hp⟩ := (level_le_iff_near (Nat.lt_succ_self R)).mp hv
    obtain ⟨r, hr, q, hq⟩ := walk_to_endVerts_after_deletion F hs p
    let r' : T := f ⟨r, hr⟩
    have hroot : ℓ (r' : V) = 0 := level_zero_of_mem hr
    obtain ⟨q', hq'⟩ := exists_induced_walk_of_level_zero hℓ
      (v := v) (root := r') hroot q (hq.trans hp)
    refine ⟨r', ?_, q', hq'.le.trans (hq.trans hp)⟩
    exact Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_attach S _, rfl⟩
  obtain ⟨Q_H, hQH, hQcard, hQmono⟩ :=
    exists_radius_certificate_of_badEdges hBH c0 hc S_H hScard hcover hfar
  let incl : H →g G := (SimpleGraph.Embedding.induce T).toHom
  exact ⟨Q_H.image (Sym2.map incl),
    image_certificate incl Subtype.val_injective hQH hQcard hQmono⟩

end Erdos74.Certificates

/-
# Local repair of Boolean colorings and finite edge certificates

The induction either repairs a Boolean coloring, using a third color only in a
bounded neighborhood of its bad edges, or produces a bounded edge certificate.
- a smaller-error coloring of a ball is repaired recursively and glued through
  a clean four-level annulus;
- if the ball retains every error, bounded-radius branching gives a certificate.
-/

namespace Erdos74.Certificates

/-- The radius needed to repair `t` bad edges, unless a certificate is found. -/
def repairRadius : ℕ → ℕ
  | 0 => 0
  | t + 1 => (2 * (t + 1) - 1) * (2 * repairRadius t + 4)

@[simp] theorem repairRadius_zero : repairRadius 0 = 0 := rfl

@[simp] theorem repairRadius_succ (t : ℕ) :
    repairRadius (t + 1) = (2 * (t + 1) - 1) * (2 * repairRadius t + 4) := rfl

theorem repairRadius_le_succ (t : ℕ) : repairRadius t ≤ repairRadius (t + 1) := by
  rw [repairRadius_succ]
  have hfac : 1 ≤ 2 * (t + 1) - 1 := by omega
  calc
    repairRadius t ≤ 2 * repairRadius t + 4 := by omega
    _ = 1 * (2 * repairRadius t + 4) := by simp
    _ ≤ (2 * (t + 1) - 1) * (2 * repairRadius t + 4) :=
      Nat.mul_le_mul_right _ hfac

theorem repairRadius_monotone : Monotone repairRadius :=
  monotone_nat_of_le_succ repairRadius_le_succ

theorem repairRadius_pred {t : ℕ} (ht : 0 < t) :
    repairRadius t = (2 * t - 1) * (2 * repairRadius (t - 1) + 4) := by
  cases t with
  | zero => omega
  | succ t => simp

/-- Edge-count threshold for a certificate at level `t`. -/
def certificateBound (t : ℕ) : ℕ := radiusCertificateBound t (repairRadius t)

universe u
variable {V : Type u}

/-- The induced ball used in the repair induction. -/
def colorBall (G : SimpleGraph V) [Finite V] (c : V → Bool) (R : ℕ) : Set V :=
  {v | level G (endVerts (badEdges G c)) (R + 1) v ≤ R}

/-- A recursively repaired coloring of a ball extends through an annulus which
contains no new bad-edge endpoints. -/
theorem extend_repaired_ball [Finite V]
    (G : SimpleGraph V) (c : V → Bool) {t r R : ℕ}
    (ht : 0 < t) (hR : R = (2 * t - 1) * (2 * r + 4))
    (c₁ : colorBall G c R → Bool)
    (herr : (badEdges (G.induce (colorBall G c R)) c₁).card < t)
    (γ : (G.induce (colorBall G c R)).Coloring (Fin 3))
    (hloc : ∀ v, ¬ Near (G.induce (colorBall G c R))
      (endVerts (badEdges (G.induce (colorBall G c R)) c₁)) r v →
      γ v = AnnulusGluing.boolColor (c₁ v)) :
    ∃ C : G.Coloring (Fin 3), ∀ v,
      ¬ Near G (endVerts (badEdges G c)) R v →
      C v = AnnulusGluing.boolColor (c v) := by
  classical
  let ℓ : V → ℕ := level G (endVerts (badEdges G c)) (R + 1)
  let T : Set V := colorBall G c R
  let H : SimpleGraph T := G.induce T
  let Z : Finset T := endVerts (badEdges H c₁)
  have hZ : Z.card ≤ 2 * t - 2 := by
    have hz := card_endVerts_le (badEdges H c₁)
    change (badEdges H c₁).card < t at herr
    change Z.card ≤ 2 * (badEdges H c₁).card at hz
    omega
  obtain ⟨a, ha, habound, hsep⟩ :=
    exists_separated_annulus Z (fun v : T => ℓ v) (r := r) ht hZ
  have hab : a + 3 ≤ R := by simpa only [hR] using habound
  have hlevel : ∀ {u v : V}, G.Adj u v → ℓ u ≤ ℓ v + 1 :=
    fun h => level_adj_le h
  have hlevelH : ∀ {u v : T}, H.Adj u v → ℓ u ≤ ℓ v + 1 :=
    fun h => hlevel h
  have havoid (v : T) (hvlo : a ≤ ℓ v) (hvhi : ℓ v ≤ a + 3) :
      ¬ Near H Z r v := by
    rintro ⟨z, hz, p, hp⟩
    have hvz := walk_level_ineq hlevelH p
    have hzv := walk_level_ineq hlevelH p.reverse
    simp only [SimpleGraph.Walk.length_reverse] at hzv
    rcases hsep z hz (ℓ v) hvlo hvhi with h | h <;> omega
  let γ₀ (v : V) : Fin 3 :=
    if h : ℓ v ≤ R then γ ⟨v, h⟩ else AnnulusGluing.boolColor (c v)
  let c₀ (v : V) : Bool := if h : ℓ v ≤ R then c₁ ⟨v, h⟩ else c v
  have hγ : ∀ {u v : V}, G.Adj u v → ℓ u ≤ a → ℓ v ≤ a → γ₀ u ≠ γ₀ v := by
    intro u v huv hu hv
    have huR : ℓ u ≤ R := by omega
    have hvR : ℓ v ≤ R := by omega
    dsimp only [γ₀]
    rw [dif_pos huR, dif_pos hvR]
    exact γ.valid (show H.Adj ⟨u, huR⟩ ⟨v, hvR⟩ from huv)
  have hc : ∀ {u v : V}, G.Adj u v → a ≤ ℓ u → a ≤ ℓ v → c u ≠ c v := by
    intro u v huv hu _
    apply proper_off_badEdges huv
    intro hus
    have hzero : ℓ u = 0 := level_zero_of_mem hus
    omega
  have hc₀ : ∀ {u v : V}, G.Adj u v →
      a ≤ ℓ u → ℓ u ≤ a + 3 → a ≤ ℓ v → ℓ v ≤ a + 3 → c₀ u ≠ c₀ v := by
    intro u v huv hulo huhi hvlo hvhi
    have huR : ℓ u ≤ R := by omega
    have hvR : ℓ v ≤ R := by omega
    dsimp only [c₀]
    rw [dif_pos huR, dif_pos hvR]
    apply proper_off_badEdges (G := H) (c := c₁)
      (show H.Adj ⟨u, huR⟩ ⟨v, hvR⟩ from huv)
    intro huZ
    exact havoid ⟨u, huR⟩ hulo huhi (near_of_mem huZ)
  have hmatch : ∀ v, ℓ v = a → γ₀ v = AnnulusGluing.boolColor (c₀ v) := by
    intro v hv
    have hvR : ℓ v ≤ R := by omega
    dsimp only [γ₀, c₀]
    rw [dif_pos hvR, dif_pos hvR]
    apply hloc
    exact havoid ⟨v, hvR⟩ (show a ≤ ℓ v by omega) (show ℓ v ≤ a + 3 by omega)
  obtain ⟨C, _, houter⟩ := AnnulusGluing.exists_coloring hlevel hγ hc hc₀ hmatch
  refine ⟨C, ?_⟩
  intro v hv
  apply houter
  have hcap : ℓ v = R + 1 := level_eq_cap_of_not_near hv
  omega

/-- Strong local repair alternative. The certificate need not itself be
non-three-colorable; its lower bound is retained unchanged by the induction. -/
theorem localized_coloring_or_certificate (t : ℕ) :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (c : V → Bool),
      (badEdges G c).card = t →
      (∃ C : G.Coloring (Fin 3), ∀ v,
        ¬ Near G (endVerts (badEdges G c)) (repairRadius t) v →
        C v = AnnulusGluing.boolColor (c v)) ∨
      ∃ k > 0, ∃ Q : Finset (Sym2 V),
        (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ certificateBound k ∧
          ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro V _ G c hcount
    by_cases ht : t = 0
    · have hFempty : badEdges G c = ∅ := Finset.card_eq_zero.mp (hcount.trans ht)
      have hc : ∀ {v w : V}, G.Adj v w → c v ≠ c w := by
        intro v w hvw heq
        have hmem := (mem_badEdges G c v w).mpr ⟨hvw, heq⟩
        simp only [hFempty, Finset.notMem_empty] at hmem
      let C : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk
        (fun v => AnnulusGluing.boolColor (c v))
        (fun h => AnnulusGluing.boolColor_injective.ne (hc h))
      exact Or.inl ⟨C, fun _ _ => rfl⟩
    have htpos : 0 < t := Nat.pos_of_ne_zero ht
    let T : Set V := colorBall G c (repairRadius t)
    let H : SimpleGraph T := G.induce T
    by_cases hall : ∀ d : T → Bool, t ≤ (badEdges H d).card
    · obtain ⟨Q, hQ, hcard, hmono⟩ :=
        exists_ball_certificate_of_badEdges G c (R := repairRadius t) hcount hall
      exact Or.inr ⟨t, htpos, Q, hQ, hcard, hmono⟩
    push_neg at hall
    obtain ⟨c₁, hs⟩ := hall
    let s := (badEdges H c₁).card
    have hslt : s < t := hs
    rcases ih s hslt T H c₁ rfl with hgood | hcert
    · obtain ⟨γ, hγ⟩ := hgood
      have hrad : repairRadius s ≤ repairRadius (t - 1) :=
        repairRadius_monotone (by omega)
      apply Or.inl
      apply extend_repaired_ball G c htpos (repairRadius_pred htpos) c₁ hs γ
      intro v hv
      apply hγ
      intro hvnear
      exact hv (near_mono hrad hvnear)
    · obtain ⟨k, hk, Q, hQ, hcard, hmono⟩ := hcert
      let φ : H →g G := (SimpleGraph.Embedding.induce T).toHom
      have hφ : Function.Injective φ := Subtype.val_injective
      obtain ⟨hQ', hcard', hmono'⟩ := image_certificate φ hφ hQ hcard hmono
      exact Or.inr ⟨k, hk, Q.image (Sym2.map φ), hQ', hcard', hmono'⟩

/-- Every finite graph which is not three-colorable has a uniformly bounded
finite edge certificate. -/
theorem finite_non_three_colorable_certificate
    (V : Type u) [Finite V] (G : SimpleGraph V) (hG : ¬ G.Colorable 3) :
    ∃ k > 0, ∃ Q : Finset (Sym2 V),
      (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ certificateBound k ∧
        ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card := by
  rcases localized_coloring_or_certificate (badEdges G (fun _ => false)).card
      V G (fun _ => false) rfl with h | h
  · obtain ⟨C, _⟩ := h
    exact (hG ⟨C⟩).elim
  · exact h

end Erdos74.Certificates

/-
# Arbitrarily slow divergent natural-number budgets

For every sequence `N : ℕ → ℕ`, `slowBudget N` tends to infinity but is less
than `k` on the whole interval `n ≤ N k`, for every `k ≥ 1`. No monotonicity
or growth hypothesis on `N` is needed.

We form the monotone majorant `M k = k + 1 + ∑ i ≤ k, N i` and take the
least `j` such that `n ≤ M (j + 1)`. The offset permits the candidate `k - 1`
when `n ≤ N k`; excluding `k = 0` is essential for a strict natural-number
budget bound. This file does not import or depend on `Submission.Spec`.
-/

namespace Erdos74Aux

open Filter

/-- A monotone, unbounded majorant of an arbitrary sequence of natural numbers. -/
def budgetMajorant (N : ℕ → ℕ) (k : ℕ) : ℕ :=
  k + 1 + (Finset.range (k + 1)).sum N

/-- The majorant dominates the original sequence at every index. -/
theorem le_budgetMajorant (N : ℕ → ℕ) (k : ℕ) :
    N k ≤ budgetMajorant N k := by
  have h : N k ≤ (Finset.range (k + 1)).sum N :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (N i))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  unfold budgetMajorant
  omega

/-- The prefix sums are monotone even if `N` is not. -/
theorem budgetMajorant_monotone (N : ℕ → ℕ) : Monotone (budgetMajorant N) := by
  intro i j hij
  unfold budgetMajorant
  exact Nat.add_le_add (Nat.add_le_add_right hij 1)
    (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right hij 1)))

/-- The linear term makes the inverse search terminate for every input. -/
theorem exists_le_budgetMajorant (N : ℕ → ℕ) (n : ℕ) :
    ∃ j : ℕ, n ≤ budgetMajorant N (j + 1) := by
  refine ⟨n, ?_⟩
  unfold budgetMajorant
  omega

/-- The least index `j` for which `n ≤ budgetMajorant N (j + 1)`. -/
def slowBudget (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.find (exists_le_budgetMajorant N n)

/-- The defining upper bound at the least index. -/
theorem slowBudget_spec (N : ℕ → ℕ) (n : ℕ) :
    n ≤ budgetMajorant N (slowBudget N n + 1) :=
  Nat.find_spec (exists_le_budgetMajorant N n)

/-- The budget is strictly below `k` throughout the prescribed initial interval. -/
theorem slowBudget_lt_of_le (N : ℕ → ℕ) {k n : ℕ}
    (hk : 1 ≤ k) (hn : n ≤ N k) : slowBudget N n < k := by
  have hbound : n ≤ budgetMajorant N ((k - 1) + 1) := by
    rw [Nat.sub_add_cancel hk]
    exact hn.trans (le_budgetMajorant N k)
  have hfind : slowBudget N n ≤ k - 1 :=
    Nat.find_min' (exists_le_budgetMajorant N n) hbound
  omega

/-- The concrete budget can also be chosen monotone. -/
theorem slowBudget_monotone (N : ℕ → ℕ) : Monotone (slowBudget N) := by
  intro n m hnm
  exact Nat.find_min' (exists_le_budgetMajorant N n)
    (hnm.trans (slowBudget_spec N m))

/-- Beyond `budgetMajorant N k`, the budget is at least `k`. -/
theorem le_slowBudget_of_majorant_lt (N : ℕ → ℕ) {k n : ℕ}
    (hn : budgetMajorant N k < n) : k ≤ slowBudget N n := by
  by_contra h
  have hle : slowBudget N n + 1 ≤ k := by omega
  have hbound := (slowBudget_spec N n).trans (budgetMajorant_monotone N hle)
  omega

/-- Despite all the prescribed upper bounds, the budget diverges to infinity. -/
theorem slowBudget_tendsto (N : ℕ → ℕ) :
    Tendsto (slowBudget N) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (budgetMajorant N k + 1)] with n hn
  exact le_slowBudget_of_majorant_lt N (by omega)

/-- An arbitrary sequence of finite thresholds admits a divergent budget that
is strictly less than `k` up to the `k`th threshold, for every positive `k`. -/
theorem exists_slow_divergent_budget (N : ℕ → ℕ) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ k ≥ 1, ∀ n, n ≤ N k → f n < k := by
  exact ⟨slowBudget N, slowBudget_tendsto N,
    fun _ hk _ hn => slowBudget_lt_of_le N hk hn⟩

end Erdos74Aux

/-
# From finite edge certificates to a slow profile obstruction

Suppose every finite graph that is not three-colorable has a positive-parameter
Boolean edge certificate of size at most `N k`. The divergent budget
`slowBudget (fun k => 2 * N k)` then forces three-colorability on finite graphs:
the certificate is supported on at most `2 * N k` vertices, where the profile
allows fewer than `k` edge deletions, contradicting the certificate.

The compactness bridge extends this conclusion to arbitrary graphs and gives
the exact negation of the infinite-chromatic-profile assertion. This is a
conditional reduction: it assumes the finite certificate theorem and uses
neither a localization theorem nor a radius bound.
-/

namespace Erdos74.Certificates

open Filter

universe u
variable {V : Type u}

/-- A Boolean edge certificate lower-bounds any profile budget at the number
of its endpoints. The ambient graph need not be finite. -/
theorem le_profile_of_certificate {G : SimpleGraph V} {f : ℕ → ℕ}
    (hG : ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    {Q : Finset (Sym2 V)} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    k ≤ f (endVerts Q).card := by
  let S := endVerts Q
  let A : G.Subgraph := (⊤ : G.Subgraph).induce (S : Set V)
  have hA : A.verts.Finite := S.finite_toSet
  obtain ⟨E, _, hE, hcard, hbip⟩ :=
    SimpleGraph.exists_finite_bipartite_deletion_of_profile_le hG A hA
  have hcoe : (A.deleteEdges E).coe = (G.deleteEdges E).induce (S : Set V) := by
    ext v w
    simp [A, Function.Embedding.subtype]
  have hbip' : ((G.deleteEdges E).induce (S : Set V)).IsBipartite := by
    simpa only [hcoe] using hbip
  have hkE : k ≤ E.ncard :=
    le_ncard_ambient_deletion_of_certificate hQ Set.Subset.rfl hmono hE hbip'
  have hcard' : E.ncard ≤ f S.card := by
    simpa [A] using hcard
  exact hkE.trans hcard'

/-- A graph with the stated certificate alternative is three-colorable if
its profile is bounded by the slow budget for the endpoint thresholds.
No finiteness assumption is needed beyond the certificate alternative itself. -/
theorem colorable_of_profile_le_slowBudget_of_certificates (N : ℕ → ℕ)
    {G : SimpleGraph V}
    (hcertificate : ¬ G.Colorable 3 → ∃ k > 0, ∃ Q : Finset (Sym2 V),
      (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ N k ∧
        ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    (hG : ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤
      Erdos74Aux.slowBudget (fun k => 2 * N k) n) : G.Colorable 3 := by
  classical
  by_contra hcolor
  obtain ⟨k, hk, Q, hQ, hQcard, hmono⟩ := hcertificate hcolor
  have hsize : (endVerts Q).card ≤ 2 * N k :=
    (card_endVerts_le Q).trans (Nat.mul_le_mul_left 2 hQcard)
  have hlt : Erdos74Aux.slowBudget (fun k => 2 * N k) (endVerts Q).card < k :=
    Erdos74Aux.slowBudget_lt_of_le (fun k => 2 * N k)
      (Nat.succ_le_of_lt hk) hsize
  exact (Nat.not_le_of_lt hlt) (le_profile_of_certificate hG hQ hmono)

/-- Uniform finite edge certificates refute the infinite-chromatic-profile
assertion for the explicit divergent budget `slowBudget (fun k => 2 * N k)`.
The finite certificate hypothesis and the conclusion use the same arbitrary
universe. No monotonicity or growth assumption on `N` is required. -/
theorem not_erdos74_of_finite_certificates (N : ℕ → ℕ)
    (hfinite : ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      ¬ G.Colorable 3 → ∃ k > 0, ∃ Q : Finset (Sym2 V),
        (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ N k ∧
          ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) := by
  exact SimpleGraph.not_forall_exists_infinite_chromatic_profile
    (Erdos74Aux.slowBudget_tendsto (fun k => 2 * N k))
    (fun V _ G hG =>
      colorable_of_profile_le_slowBudget_of_certificates N (hfinite V G) hG)

end Erdos74.Certificates

theorem Erdos74.erdos_74.disproof : ¬ (type_of% @Erdos74.erdos_74) := by
  exact Erdos74.Certificates.not_erdos74_of_finite_certificates
    Erdos74.Certificates.certificateBound
    Erdos74.Certificates.finite_non_three_colorable_certificate
