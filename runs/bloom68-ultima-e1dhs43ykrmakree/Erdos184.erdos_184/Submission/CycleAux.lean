import Submission.DecompositionAux
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Verified cycle and decomposition infrastructure

These are support lemmas for the definitions in `Submission.Spec`. No unproved
statement from that file is used. In particular, none of the results here proves
the uniform linear bound in Erdős problem 184.

`EdgePartition` records a partition of a specified set of *ambient* edges. It is
used to transport intrinsic subgraph decompositions and to combine or replace
pieces without confusing `Sym2 H.verts` with `Sym2 V`.
-/

open SimpleGraph
open scoped Classical

namespace Erdos184.CycleAux

open DecompositionAux

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {G' : SimpleGraph W}

section Cycles

variable [Fintype V] {x : V} {p : G.Walk x x}

/-- The intrinsic graph of a simple cyclic walk is 2-regular. -/
theorem cycle_toSubgraph_isRegularOfDegree_two (hp : p.IsCycle) :
    p.toSubgraph.coe.IsRegularOfDegree 2 := by
  intro v
  rw [Subgraph.coe_degree, Subgraph.degree]
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
    hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp v.property)

/-- A cyclic walk gives a valid cycle piece in the precise sense of the spec. -/
theorem cycle_toSubgraph_isCycleOrEdge (hp : p.IsCycle) :
    IsCycleOrEdge p.toSubgraph.coe := by
  refine Or.inl ⟨p.toSubgraph_connected.coe, ?_⟩
  intro v
  simpa only [Subgraph.coe_degree] using cycle_toSubgraph_isRegularOfDegree_two hp v

omit [Fintype V] in
/-- A trail uses each of its ambient edges once. -/
theorem trail_toSubgraph_edgeSet_ncard {a b : V} {q : G.Walk a b} (hq : q.IsTrail) :
    q.toSubgraph.edgeSet.ncard = q.length := by
  have he : q.toSubgraph.edgeSet = (q.edges.toFinset : Set (Sym2 V)) := by
    ext e
    simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup hq.edges_nodup, q.length_edges]

omit [Fintype V] in
/-- In particular every cycle piece has at least three ambient edges. -/
theorem cycle_toSubgraph_three_le_edgeSet_ncard (hp : p.IsCycle) :
    3 ≤ p.toSubgraph.edgeSet.ncard := by
  rw [trail_toSubgraph_edgeSet_ncard hp.isTrail]
  exact hp.three_le_length

end Cycles

section Transport

/-- Mapping a subgraph along an injective homomorphism preserves its intrinsic graph,
not just its ambient edges. -/
noncomputable def subgraphMapIso (f : G →g G') (hf : Function.Injective f) (H : G.Subgraph) :
    H.coe ≃g (H.map f).coe where
  toEquiv := Equiv.Set.image f H.verts hf
  map_rel_iff' := by
    intro a b
    change (∃ c d, H.Adj c d ∧ f c = f a ∧ f d = f b) ↔ H.Adj a b
    constructor
    · rintro ⟨c, d, hcd, hc, hd⟩
      simpa only [hf hc, hf hd] using hcd
    · intro hab
      exact ⟨a, b, hab, rfl, rfl⟩

/-- Graph isomorphisms preserve the two alternatives in `IsCycleOrEdge`. -/
theorem isCycleOrEdge_iso_iff [Fintype V] [Fintype W] (e : G ≃g G') :
    IsCycleOrEdge G ↔ IsCycleOrEdge G' := by
  have hreg (f : G ≃g G') (h : G.IsRegularOfDegree 2) : G'.IsRegularOfDegree 2 := by
    intro w
    obtain ⟨v, rfl⟩ := f.surjective w
    rw [f.degree_eq]
    exact h v
  constructor
  · rintro (⟨hc, hr⟩ | he)
    · exact Or.inl ⟨e.connected_iff.mp hc, hreg e hr⟩
    · exact Or.inr (e.card_edgeFinset_eq.symm.trans he)
  · rintro (⟨hc, hr⟩ | he)
    · refine Or.inl ⟨e.connected_iff.mpr hc, ?_⟩
      intro v
      rw [← e.degree_eq]
      exact hr (e v)
    · exact Or.inr (e.card_edgeFinset_eq.trans he)

/-- Validity of pieces is preserved by injective subgraph transport. -/
theorem isCycleOrEdge_map [Fintype V] [Fintype W] (f : G →g G')
    (hf : Function.Injective f) {H : G.Subgraph} (hH : IsCycleOrEdge H.coe) :
    IsCycleOrEdge (H.map f).coe :=
  (isCycleOrEdge_iso_iff (subgraphMapIso f hf H)).mp hH

/-- A finite family partitions the specified set of ambient edges. Vertices need
not be disjoint, and isolated vertices are irrelevant to the covering condition. -/
def EdgePartition (D : Finset G.Subgraph) (s : Set (Sym2 V)) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
    (⋃ H ∈ D, H.edgeSet) = s

@[simp]
theorem edgePartition_ambient_iff (D : Finset G.Subgraph) :
    EdgePartition D G.edgeSet ↔ IsDecomposition G D := Iff.rfl

/-- Each piece of a partition uses only the edges being partitioned. -/
theorem EdgePartition.edgeSet_subset {D : Finset G.Subgraph} {s : Set (Sym2 V)}
    (hD : EdgePartition D s) {H : G.Subgraph} (hH : H ∈ D) : H.edgeSet ⊆ s := by
  intro e he
  rw [← hD.2]
  exact Set.mem_iUnion₂.mpr ⟨H, hH, he⟩

/-- Finite partitions of disjoint ambient edge sets can be united. -/
theorem EdgePartition.union {D E : Finset G.Subgraph} {s t : Set (Sym2 V)}
    (hD : EdgePartition D s) (hE : EdgePartition E t) (hst : Disjoint s t) :
    EdgePartition (D ∪ E) (s ∪ t) := by
  constructor
  · rw [Finset.coe_union]
    refine hD.1.union hE.1 ?_
    intro H hH K hK _
    exact hst.mono (hD.edgeSet_subset hH) (hE.edgeSet_subset hK)
  · ext e
    simp only [Set.mem_iUnion, Finset.mem_union, exists_prop, Set.mem_union]
    rw [← hD.2, ← hE.2]
    simp only [Set.mem_iUnion, exists_prop]
    aesop

@[simp]
theorem edgePartition_singleton (H : G.Subgraph) : EdgePartition {H} H.edgeSet := by
  constructor
  · simp
  · simp

/-- Erasing one member leaves a partition of the complementary edges. -/
theorem EdgePartition.erase {D : Finset G.Subgraph} {s : Set (Sym2 V)}
    (hD : EdgePartition D s) {H : G.Subgraph} (hH : H ∈ D) :
    EdgePartition (D.erase H) (s \ H.edgeSet) := by
  constructor
  · exact hD.1.subset (by simp)
  · ext e
    constructor
    · intro he
      obtain ⟨K, hK, heK⟩ := Set.mem_iUnion₂.mp he
      obtain ⟨hne, hKD⟩ := Finset.mem_erase.mp hK
      refine ⟨hD.edgeSet_subset hKD heK, ?_⟩
      exact fun heH ↦ (Set.disjoint_left.mp (hD.1 hKD hH hne)) heK heH
    · rintro ⟨hes, heH⟩
      rw [← hD.2] at hes
      obtain ⟨K, hKD, heK⟩ := Set.mem_iUnion₂.mp hes
      refine Set.mem_iUnion₂.mpr ⟨K, Finset.mem_erase.mpr ⟨?_, hKD⟩, heK⟩
      rintro rfl
      exact heH heK

/-- Transport a finite partition along an injective homomorphism. The target
edge set is explicitly an image under `Sym2.map`. -/
theorem EdgePartition.map {D : Finset G.Subgraph} {s : Set (Sym2 V)}
    (hD : EdgePartition D s) (f : G →g G') (hf : Function.Injective f) :
    EdgePartition (D.image (Subgraph.map f)) (Sym2.map f '' s) := by
  constructor
  · intro H hH K hK hne
    obtain ⟨H, hHD, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨K, hKD, rfl⟩ := Finset.mem_image.mp hK
    change Disjoint (H.map f).edgeSet (K.map f).edgeSet
    rw [Subgraph.edgeSet_map, Subgraph.edgeSet_map,
      Set.disjoint_image_iff (Sym2.map.injective hf)]
    exact hD.1 hHD hKD (fun h ↦ hne (congrArg (Subgraph.map f) h))
  · rw [← hD.2]
    ext e
    simp only [Set.mem_iUnion, Finset.mem_image, Set.mem_image, exists_prop]
    aesop

/-- An intrinsic decomposition of `H.coe` transports to a partition of `H.edgeSet`
in the original ambient graph. -/
theorem edgePartition_map_subgraph (H : G.Subgraph) (D : Finset H.coe.Subgraph)
    (hD : IsDecomposition H.coe D) :
    EdgePartition (D.image (Subgraph.map H.hom)) H.edgeSet := by
  have h := EdgePartition.map hD H.hom H.hom_injective
  simpa only [Subgraph.coe_hom, H.image_coe_edgeSet_coe] using h

/-- A decomposition in a smaller graph on the same vertex type can be lifted
without adding edges or vertices to any individual piece. -/
theorem edgePartition_map_ofLE {H : SimpleGraph V} (hHG : H ≤ G)
    (D : Finset H.Subgraph) (hD : IsDecomposition H D) :
    EdgePartition (D.image (Subgraph.map (Hom.ofLE hHG))) H.edgeSet := by
  have h := EdgePartition.map hD (Hom.ofLE hHG) (by exact Function.injective_id)
  simpa only [Hom.coe_ofLE, Sym2.map_id, Set.image_id] using h

/-- Union of intrinsic decompositions of edge-disjoint ambient subgraphs. -/
theorem isDecomposition_union_subgraphs (H K : G.Subgraph)
    (D : Finset H.coe.Subgraph) (E : Finset K.coe.Subgraph)
    (hD : IsDecomposition H.coe D) (hE : IsDecomposition K.coe E)
    (hdisj : Disjoint H.edgeSet K.edgeSet) (hcover : H.edgeSet ∪ K.edgeSet = G.edgeSet) :
    IsDecomposition G
      (D.image (Subgraph.map H.hom) ∪ E.image (Subgraph.map K.hom)) := by
  have h := (edgePartition_map_subgraph H D hD).union
    (edgePartition_map_subgraph K E hE) hdisj
  simpa only [hcover, edgePartition_ambient_iff] using h

/-- Replace a member of a decomposition by any intrinsic decomposition of that
member. No vertex-disjointness or spanning-subgraph assumption is needed. -/
theorem isDecomposition_replace (D : Finset G.Subgraph) (hD : IsDecomposition G D)
    {H : G.Subgraph} (hH : H ∈ D) (E : Finset H.coe.Subgraph)
    (hE : IsDecomposition H.coe E) :
    IsDecomposition G (D.erase H ∪ E.image (Subgraph.map H.hom)) := by
  have h := (EdgePartition.erase hD hH).union (edgePartition_map_subgraph H E hE)
    (Set.disjoint_left.mpr fun _ he hmem ↦ he.2 hmem)
  have hc : (G.edgeSet \ H.edgeSet) ∪ H.edgeSet = G.edgeSet :=
    Set.diff_union_of_subset H.edgeSet_subset
  simpa only [hc, edgePartition_ambient_iff] using h

/-- Reinsert an ambient subgraph after decomposing the graph with its edges deleted.
The residual pieces are transported using the inclusion homomorphism. -/
theorem isDecomposition_insert_deleteEdges (H : G.Subgraph)
    (D : Finset (G.deleteEdges H.edgeSet).Subgraph)
    (hD : IsDecomposition (G.deleteEdges H.edgeSet) D) :
    IsDecomposition G
      (insert H (D.image (Subgraph.map (Hom.ofLE (G.deleteEdges_le H.edgeSet))))) := by
  have h := (edgePartition_singleton H).union
    (edgePartition_map_ofLE (G.deleteEdges_le H.edgeSet) D hD)
    (by rw [SimpleGraph.edgeSet_deleteEdges]
        exact Set.disjoint_left.mpr fun _ he hmem ↦ hmem.2 he)
  have hc : H.edgeSet ∪ (G.deleteEdges H.edgeSet).edgeSet = G.edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    ext e
    have hsub : e ∈ H.edgeSet → e ∈ G.edgeSet := fun he ↦ H.edgeSet_subset he
    simp only [Set.mem_union, Set.mem_diff]
    tauto
  simpa only [Finset.singleton_union, hc, edgePartition_ambient_iff] using h

section Finite

variable [Fintype V]

/-- The union construction preserves valid pieces and costs at most the sum of
the two decomposition sizes. -/
theorem exists_valid_decomposition_union_subgraphs (H K : G.Subgraph)
    (D : Finset H.coe.Subgraph) (E : Finset K.coe.Subgraph)
    (hpiecesD : ∀ J ∈ D, IsCycleOrEdge J.coe)
    (hpiecesE : ∀ J ∈ E, IsCycleOrEdge J.coe)
    (hD : IsDecomposition H.coe D) (hE : IsDecomposition K.coe E)
    (hdisj : Disjoint H.edgeSet K.edgeSet) (hcover : H.edgeSet ∪ K.edgeSet = G.edgeSet) :
    ∃ F : Finset G.Subgraph, (∀ J ∈ F, IsCycleOrEdge J.coe) ∧
      IsDecomposition G F ∧ F.card ≤ D.card + E.card := by
  refine ⟨D.image (Subgraph.map H.hom) ∪ E.image (Subgraph.map K.hom), ?_,
    isDecomposition_union_subgraphs H K D E hD hE hdisj hcover, ?_⟩
  · intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · obtain ⟨J, hJD, rfl⟩ := Finset.mem_image.mp hJ
      exact isCycleOrEdge_map H.hom H.hom_injective (hpiecesD J hJD)
    · obtain ⟨J, hJD, rfl⟩ := Finset.mem_image.mp hJ
      exact isCycleOrEdge_map K.hom K.hom_injective (hpiecesE J hJD)
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

/-- Replacement preserves validity. The size bound accounts for the erased
member of `D` and the newly inserted members of `E`. -/
theorem exists_valid_decomposition_replace (D : Finset G.Subgraph)
    (hpiecesD : ∀ J ∈ D, IsCycleOrEdge J.coe) (hD : IsDecomposition G D)
    {H : G.Subgraph} (hH : H ∈ D) (E : Finset H.coe.Subgraph)
    (hpiecesE : ∀ J ∈ E, IsCycleOrEdge J.coe) (hE : IsDecomposition H.coe E) :
    ∃ F : Finset G.Subgraph, (∀ J ∈ F, IsCycleOrEdge J.coe) ∧
      IsDecomposition G F ∧ F.card ≤ D.card - 1 + E.card := by
  refine ⟨D.erase H ∪ E.image (Subgraph.map H.hom), ?_,
    isDecomposition_replace D hD hH E hE, ?_⟩
  · intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact hpiecesD J (Finset.mem_of_mem_erase hJ)
    · obtain ⟨J, hJD, rfl⟩ := Finset.mem_image.mp hJ
      exact isCycleOrEdge_map H.hom H.hom_injective (hpiecesE J hJD)
  · calc
      _ ≤ (D.erase H).card + (E.image (Subgraph.map H.hom)).card :=
        Finset.card_union_le _ _
      _ ≤ (D.erase H).card + E.card := Nat.add_le_add_left Finset.card_image_le _
      _ = D.card - 1 + E.card := by rw [Finset.card_erase_of_mem hH]

end Finite

end Transport

section Forests

variable [Fintype V]

/-- A forest on a nonempty finite vertex type has fewer edges than vertices.
We extend it to a spanning tree of the complete graph and use the tree edge count. -/
theorem forest_edgeFinset_card_lt [Nonempty V] (hG : G.IsAcyclic) :
    G.edgeFinset.card < Fintype.card V := by
  obtain ⟨T, hGT, hT⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (G := (⊤ : SimpleGraph V)) le_top hG
  have htree : T.IsTree :=
    (connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hT
  have hcard := htree.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  omega

/-- The usual forest edge bound, including the empty vertex type. -/
theorem forest_edgeFinset_card_le_card_sub_one (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have hbot : G = ⊥ := Subsingleton.elim _ _
    simp [hbot]
  · have := forest_edgeFinset_card_lt hG
    omega

/-- The individual-edge decomposition of a finite forest has at most `|V|` pieces. -/
theorem exists_forest_decomposition (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ D.card ≤ Fintype.card V := by
  refine ⟨edgeDecomposition G, edgeDecomposition_isCycleOrEdge G,
    edgeDecomposition_isDecomposition G, ?_⟩
  rw [edgeDecomposition_card]
  exact (forest_edgeFinset_card_le_card_sub_one hG).trans (Nat.sub_le _ _)

/-- The attained minimum decomposition number obeys the forest bound as well. -/
theorem decompositionNumber_le_card_of_isAcyclic (hG : G.IsAcyclic) :
    decompositionNumber G ≤ Fintype.card V :=
  (decompositionNumber_le_edgeFinset_card G).trans
    ((forest_edgeFinset_card_le_card_sub_one hG).trans (Nat.sub_le _ _))

/-- A finite forest with all degrees even has no edges. The degree-sum argument
is applied only to the support, so isolated vertices cause no exception. -/
theorem acyclic_eq_bot_of_even_degrees (hG : G.IsAcyclic)
    (heven : ∀ v, Even (G.degree v)) : G = ⊥ := by
  by_contra hbot
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hbot
  letI : Nonempty G.support := ⟨⟨a, b, hab⟩⟩
  have hforest := forest_edgeFinset_card_lt (hG.induce G.support)
  have hdeg : ∀ v : G.support, 2 ≤ (G.induce G.support).degree v := by
    intro v
    rw [SimpleGraph.degree_induce_support]
    have hpos := (G.degree_pos_iff_mem_support v).mpr v.property
    have hpar := Nat.even_iff.mp (heven v)
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦ hdeg v)
  have hhandshake := (G.induce G.support).sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

/-- Every nonempty-edge finite even graph contains a simple cyclic walk.
This is derived from the forest bound, not from Euler-tour existence. -/
theorem exists_cycle_of_even_degrees_ne_bot (heven : ∀ v, Even (G.degree v))
    (hbot : G ≠ ⊥) : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  by_contra hcycle
  apply hbot
  apply acyclic_eq_bot_of_even_degrees (heven := heven)
  intro v p hp
  exact hcycle ⟨v, p, hp⟩

end Forests

section DeleteCycles

variable [Fintype V]

/-- Removing the ambient edges of a subgraph subtracts its degree at each vertex. -/
theorem degree_deleteEdges_subgraph (H : G.Subgraph) (v : V) :
    (G.deleteEdges H.edgeSet).degree v = G.degree v - H.degree v := by
  have hN : (G.deleteEdges H.edgeSet).neighborFinset v =
      G.neighborFinset v \ (H.neighborSet v).toFinset := by
    ext w
    simp
  rw [SimpleGraph.degree, hN, Finset.card_sdiff_of_subset,
    SimpleGraph.card_neighborFinset_eq_degree, Subgraph.finset_card_neighborSet_eq_degree]
  intro w hw
  have hwH : H.Adj v w := by simpa only [Set.mem_toFinset, Subgraph.mem_neighborSet] using hw
  exact (G.mem_neighborFinset v w).mpr (H.adj_sub hwH)

/-- The cycle subgraph has degree two on its vertices and zero elsewhere, hence
has even degree at every ambient vertex. -/
theorem cycle_toSubgraph_even_degree {x : V} {p : G.Walk x x} (hp : p.IsCycle) (v : V) :
    Even (p.toSubgraph.degree v) := by
  by_cases hv : v ∈ p.toSubgraph.verts
  · have hdeg := cycle_toSubgraph_isRegularOfDegree_two hp ⟨v, hv⟩
    rw [Subgraph.coe_degree] at hdeg
    rw [hdeg]
    decide
  · rw [Subgraph.degree_of_notMem_verts hv]
    decide

/-- Removing a cycle preserves the parity of every degree. -/
theorem even_degrees_delete_cycle (heven : ∀ v, Even (G.degree v))
    {x : V} {p : G.Walk x x} (hp : p.IsCycle) :
    ∀ v, Even ((G.deleteEdges p.toSubgraph.edgeSet).degree v) := by
  intro v
  rw [degree_deleteEdges_subgraph]
  exact (Nat.even_sub (p.toSubgraph.degree_le v)).mpr
    ⟨fun _ ↦ cycle_toSubgraph_even_degree hp v, fun _ ↦ heven v⟩

/-- Exact edge-count bookkeeping for deleting an ambient subgraph. -/
theorem edgeFinset_card_deleteEdges_add (H : G.Subgraph) :
    (G.deleteEdges H.edgeSet).edgeFinset.card + H.edgeSet.ncard = G.edgeFinset.card := by
  rw [← Set.ncard_coe_finset (G.deleteEdges H.edgeSet).edgeFinset,
    SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
    Set.ncard_diff_add_ncard_of_subset H.edgeSet_subset,
    ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

/-- Deleting a cycle strictly decreases the finite number of edges. -/
theorem cycle_deleteEdges_card_lt {x : V} {p : G.Walk x x} (hp : p.IsCycle) :
    (G.deleteEdges p.toSubgraph.edgeSet).edgeFinset.card < G.edgeFinset.card := by
  have hcount := edgeFinset_card_deleteEdges_add p.toSubgraph
  have hthree := cycle_toSubgraph_three_le_edgeSet_ncard hp
  omega

end DeleteCycles

section EvenGraphs

variable [Fintype V]

/-- A finite even graph has an edge-disjoint decomposition by actual simple cyclic
walks, with three times as many pieces at most as there are edges. The proof is
strong induction on the edge count, removing a cycle at each nonzero step. -/
theorem exists_cycle_walk_decomposition_of_even_degrees (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph = H) ∧
      IsDecomposition G D ∧ 3 * D.card ≤ G.edgeFinset.card := by
  induction hn : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hbot : G = ⊥
    · subst G
      refine ⟨∅, by simp, ?_, by simp⟩
      simp [IsDecomposition]
    obtain ⟨x, p, hp⟩ := exists_cycle_of_even_degrees_ne_bot heven hbot
    let R := G.deleteEdges p.toSubgraph.edgeSet
    have hlt : R.edgeFinset.card < n := by
      rw [← hn]
      exact cycle_deleteEdges_card_lt hp
    obtain ⟨D, hcycles, hD, hcard⟩ := ih R.edgeFinset.card hlt R
      (by
        intro v
        convert even_degrees_delete_cycle heven hp v using 1
        congr 1
        exact Subsingleton.elim _ _)
      (by simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset])
    let f : R →g G := Hom.ofLE (G.deleteEdges_le p.toSubgraph.edgeSet)
    refine ⟨insert p.toSubgraph (D.image (Subgraph.map f)), ?_,
      isDecomposition_insert_deleteEdges p.toSubgraph D hD, ?_⟩
    · intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact ⟨x, p, hp, rfl⟩
      · obtain ⟨K, hKD, rfl⟩ := Finset.mem_image.mp hH
        obtain ⟨y, q, hq, rfl⟩ := hcycles K hKD
        exact ⟨f y, q.map f, Walk.IsCycle.map (by exact Function.injective_id) hq,
          q.toSubgraph_map f⟩
    · have hsize : (insert p.toSubgraph (D.image (Subgraph.map f))).card ≤ D.card + 1 :=
        (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
      have hcount := edgeFinset_card_deleteEdges_add p.toSubgraph
      have hthree := cycle_toSubgraph_three_le_edgeSet_ncard hp
      change 3 * D.card ≤ (G.deleteEdges p.toSubgraph.edgeSet).edgeFinset.card at hcard
      omega

/-- The pure-cycle decomposition satisfies the spec's notion of a cycle, as well
as its exact ambient edge partition requirement. The bound is `⌊m / 3⌋`, not a
linear bound in the number of vertices. -/
theorem exists_pure_cycle_decomposition (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ G.edgeFinset.card / 3 := by
  obtain ⟨D, hcycles, hD, hcard⟩ := exists_cycle_walk_decomposition_of_even_degrees G heven
  refine ⟨D, ?_, ?_, hD, ?_⟩
  · intro H hH
    obtain ⟨x, p, hp, rfl⟩ := hcycles H hH
    refine ⟨p.toSubgraph_connected.coe, ?_⟩
    intro v
    simpa only [Subgraph.coe_degree] using cycle_toSubgraph_isRegularOfDegree_two hp v
  · intro H hH
    obtain ⟨x, p, hp, rfl⟩ := hcycles H hH
    exact cycle_toSubgraph_isCycleOrEdge hp
  · exact (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)

/-- The minimum number of cycle/edge pieces in a finite even graph is at most `m/3`. -/
theorem decompositionNumber_le_edges_div_three_of_even_degrees
    (heven : ∀ v, Even (G.degree v)) :
    decompositionNumber G ≤ G.edgeFinset.card / 3 := by
  obtain ⟨D, _, hpieces, hD, hcard⟩ := exists_pure_cycle_decomposition G heven
  exact (decompositionNumber_le_card G D hpieces hD).trans hcard

end EvenGraphs

/- Dependency audit: every declaration in this file is checked. Only Lean's
standard logical axioms may occur; no unproved result in the spec is used. -/

#print axioms cycle_toSubgraph_isRegularOfDegree_two
#print axioms cycle_toSubgraph_isCycleOrEdge
#print axioms trail_toSubgraph_edgeSet_ncard
#print axioms cycle_toSubgraph_three_le_edgeSet_ncard
#print axioms subgraphMapIso
#print axioms isCycleOrEdge_iso_iff
#print axioms isCycleOrEdge_map
#print axioms EdgePartition
#print axioms edgePartition_ambient_iff
#print axioms EdgePartition.edgeSet_subset
#print axioms EdgePartition.union
#print axioms edgePartition_singleton
#print axioms EdgePartition.erase
#print axioms EdgePartition.map
#print axioms edgePartition_map_subgraph
#print axioms edgePartition_map_ofLE
#print axioms isDecomposition_union_subgraphs
#print axioms isDecomposition_replace
#print axioms isDecomposition_insert_deleteEdges
#print axioms exists_valid_decomposition_union_subgraphs
#print axioms exists_valid_decomposition_replace
#print axioms forest_edgeFinset_card_lt
#print axioms forest_edgeFinset_card_le_card_sub_one
#print axioms exists_forest_decomposition
#print axioms decompositionNumber_le_card_of_isAcyclic
#print axioms acyclic_eq_bot_of_even_degrees
#print axioms exists_cycle_of_even_degrees_ne_bot
#print axioms degree_deleteEdges_subgraph
#print axioms cycle_toSubgraph_even_degree
#print axioms even_degrees_delete_cycle
#print axioms edgeFinset_card_deleteEdges_add
#print axioms cycle_deleteEdges_card_lt
#print axioms exists_cycle_walk_decomposition_of_even_degrees
#print axioms exists_pure_cycle_decomposition
#print axioms decompositionNumber_le_edges_div_three_of_even_degrees

end Erdos184.CycleAux
