import FormalConjecturesUtil

/-!
# Witness exchange for extremal forbidden-subgraph-free graphs

For an extremal `H`-free graph `G` and an `H`-free graph `F` on the same finite
vertex type, match every edge of `F \ G` to a distinct edge of `G \ F`. Each
matched pair lies in a single ordinary injective copy of `H` in `G ⊔ F`.
If both graphs are extremal, the matching is a bijection.

The Hall condition is proved by deleting the entire witness-neighborhood of
`R ⊆ F \ G` and adding `R`. This simultaneous replacement is `H`-free. There
is no claim that exchanging just one matched pair preserves freeness.

Only the host vertex type needs to be finite. In particular, no nonemptiness,
edge, or non-isolation assumption is made on `H`; freeness of `G` is supplied
by extremality, even in degenerate cases where that hypothesis is impossible.
-/

open SimpleGraph

namespace Erdos713Exchange

universe u v

variable {V : Type u} {W : Type v}

/-- Two edges are witnessed by one ordinary (not necessarily induced) injective
copy of `H` in the union of the two host graphs. -/
def Witness (H : SimpleGraph W) (G F : SimpleGraph V) (a b : Sym2 V) : Prop :=
  ∃ c : H.Copy (G ⊔ F), a ∈ c.toSubgraph.edgeSet ∧ b ∈ c.toSubgraph.edgeSet

/-- A copy cannot have all its edges in an `H`-free graph on the same vertices.
This also handles edgeless forbidden graphs: the same vertex injection would
already give a copy in the allegedly free graph. -/
lemma exists_edge_outside_of_free {H : SimpleGraph W} {G K : SimpleGraph V}
    (hG : H.Free G) (c : H.Copy K) :
    ∃ e ∈ c.toSubgraph.edgeSet, e ∉ G.edgeSet := by
  classical
  by_contra! h
  apply hG
  refine ⟨⟨⟨c, ?_⟩, c.injective⟩⟩
  intro x y hxy
  apply (G.mem_edgeSet).mp
  apply h s(c x, c y)
  rw [Copy.toSubgraph, Subgraph.edgeSet_map, Subgraph.edgeSet_top]
  exact ⟨s(x, y), hxy, rfl⟩

section Finite

variable [Fintype V] [DecidableEq V]
variable (H : SimpleGraph W) (G F : SimpleGraph V)
variable [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Edges present only in `F`, to be assigned witnesses. -/
def addedEdges : Finset (Sym2 V) := F.edgeFinset \ G.edgeFinset

/-- Edges present only in `G`, available as distinct witness partners. -/
def removedEdges : Finset (Sym2 V) := G.edgeFinset \ F.edgeFinset

/-- The neighborhood in `G \ F` of a collection of edges, for `Witness`. -/
noncomputable def witnessNeighbors (R : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact (removedEdges G F).filter (fun b => ∃ a ∈ R, Witness H G F a b)

/-- Delete all witness-neighbors of `R` from `G`, then add all edges of `R`. -/
noncomputable def exchangeGraph (R : Finset (Sym2 V)) : SimpleGraph V :=
  G.deleteEdges (witnessNeighbors H G F R : Set (Sym2 V)) ⊔
    fromEdgeSet (R : Set (Sym2 V))

variable {H G F}

lemma witnessNeighbors_subset (R : Finset (Sym2 V)) :
    witnessNeighbors H G F R ⊆ removedEdges G F := by
  classical
  exact Finset.filter_subset _ _

lemma exchangeGraph_le_sup {R : Finset (Sym2 V)} (hR : R ⊆ addedEdges G F) :
    exchangeGraph H G F R ≤ G ⊔ F := by
  classical
  refine sup_le ((G.deleteEdges_le _).trans le_sup_left) ?_
  refine le_trans ((F.fromEdgeSet_le).mpr ?_) le_sup_right
  intro e he
  exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hR he.1)).1

/-- The simultaneous replacement used in Hall's condition remains `H`-free.
A hypothetical copy would contain an added edge (by freeness of `G`) and an
edge outside `F` (by freeness of `F`), hence an edge that was deleted. -/
theorem exchangeGraph_free {R : Finset (Sym2 V)}
    (hG : H.Free G) (hF : H.Free F) (hR : R ⊆ addedEdges G F) :
    H.Free (exchangeGraph H G F R) := by
  classical
  rintro ⟨c⟩
  obtain ⟨a, hac, haG⟩ := exists_edge_outside_of_free hG c
  have haJ := c.toSubgraph.edgeSet_subset hac
  simp only [exchangeGraph, edgeSet_sup, edgeSet_deleteEdges,
    edgeSet_fromEdgeSet, Set.mem_union, Set.mem_diff, Finset.mem_coe] at haJ
  have haR : a ∈ R := haJ.elim (fun h => (haG h.1).elim) And.left
  obtain ⟨b, hbc, hbF⟩ := exists_edge_outside_of_free hF c
  have hbJ := c.toSubgraph.edgeSet_subset hbc
  simp only [exchangeGraph, edgeSet_sup, edgeSet_deleteEdges,
    edgeSet_fromEdgeSet, Set.mem_union, Set.mem_diff, Finset.mem_coe] at hbJ
  have hb : b ∈ G.edgeSet ∧ b ∉ witnessNeighbors H G F R := by
    rcases hbJ with hb | hb
    · exact hb
    · exact (hbF (SimpleGraph.mem_edgeFinset.mp
        (Finset.mem_sdiff.mp (hR hb.1)).1)).elim
  have hbB : b ∈ removedEdges G F :=
    Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hb.1,
      fun h => hbF (SimpleGraph.mem_edgeFinset.mp h)⟩
  have hab : Witness H G F a b :=
    ⟨(Copy.ofLE _ _ (exchangeGraph_le_sup hR)).comp c, hac, hbc⟩
  exact hb.2 (Finset.mem_filter.mpr ⟨hbB, a, haR, hab⟩)

open scoped Classical in
/-- Exact edge set of the simultaneous replacement. No loops are introduced,
since every added edge already belongs to the simple graph `F`. -/
lemma edgeFinset_exchangeGraph {R : Finset (Sym2 V)}
    (hR : R ⊆ addedEdges G F) :
    (exchangeGraph H G F R).edgeFinset =
      (G.edgeFinset \ witnessNeighbors H G F R) ∪ R := by
  classical
  ext e
  simp only [mem_edgeFinset, exchangeGraph, edgeSet_sup, edgeSet_deleteEdges,
    edgeSet_fromEdgeSet, Set.mem_union, Set.mem_diff, Finset.mem_union,
    Finset.mem_sdiff, mem_edgeFinset, Finset.mem_coe, Sym2.mem_diagSet_iff_isDiag]
  have hdiag (he : e ∈ R) : ¬e.IsDiag :=
    F.not_isDiag_of_mem_edgeFinset (Finset.mem_sdiff.mp (hR he)).1
  exact or_congr Iff.rfl ⟨And.left, fun he => ⟨he, hdiag he⟩⟩

/-- Hall's inequality for every subset of edges present only in `F`. -/
theorem card_le_witnessNeighbors_card {R : Finset (Sym2 V)}
    (hG : G.IsExtremal H.Free) (hF : H.Free F) (hR : R ⊆ addedEdges G F) :
    R.card ≤ (witnessNeighbors H G F R).card := by
  classical
  have hN : witnessNeighbors H G F R ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_sdiff.mp (witnessNeighbors_subset R he)).1
  have hdis : Disjoint (G.edgeFinset \ witnessNeighbors H G F R) R := by
    apply Finset.disjoint_left.mpr
    intro e he heR
    exact (Finset.mem_sdiff.mp (hR heR)).2 (Finset.mem_sdiff.mp he).1
  have hmax := hG.2 (exchangeGraph_free hG.1 hF hR)
  rw [edgeFinset_exchangeGraph (H := H) hR, Finset.card_union_of_disjoint hdis,
    Finset.card_sdiff_of_subset hN] at hmax
  have hNcard := Finset.card_le_card hN
  omega

/-- Every edge present only in `F` can be assigned a distinct edge present only
in extremal `G`, with both edges contained in one ordinary copy of `H` in
`G ⊔ F`. -/
theorem exists_injective_witness_assignment
    (hG : G.IsExtremal H.Free) (hF : H.Free F) :
    ∃ f : addedEdges G F → removedEdges G F,
      Function.Injective f ∧ ∀ a, Witness H G F a.1 (f a).1 := by
  classical
  let t : addedEdges G F → Finset (Sym2 V) :=
    fun a => (removedEdges G F).filter (Witness H G F a.1)
  have hHall : ∀ S : Finset (addedEdges G F), S.card ≤ (S.biUnion t).card := by
    intro S
    have hR : S.image Subtype.val ⊆ addedEdges G F := by
      intro a ha
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
      exact a.2
    have hN : witnessNeighbors H G F (S.image Subtype.val) = S.biUnion t := by
      ext b
      simp only [witnessNeighbors, Finset.mem_filter, Finset.mem_biUnion, t]
      constructor
      · rintro ⟨hb, e, he, heb⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        exact ⟨a, ha, hb, heb⟩
      · rintro ⟨a, ha, hb, hab⟩
        exact ⟨hb, a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hab⟩
    have h := card_le_witnessNeighbors_card hG hF hR
    rwa [Finset.card_image_of_injective _ Subtype.val_injective, hN] at h
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  refine ⟨fun a => ⟨f a, (Finset.mem_filter.mp (hmem a)).1⟩, ?_, ?_⟩
  · intro a a' h
    exact hf (congrArg Subtype.val h)
  · intro a
    exact (Finset.mem_filter.mp (hmem a)).2

/-- Two extremal `H`-free graphs have equally many edges in their two differences. -/
lemma card_addedEdges_eq_card_removedEdges
    (hG : G.IsExtremal H.Free) (hF : F.IsExtremal H.Free) :
    (addedEdges G F).card = (removedEdges G F).card := by
  exact Finset.card_sdiff_comm (Nat.le_antisymm (hG.2 hF.1) (hF.2 hG.1))

/-- If both graphs are extremal, the witness assignment can be bijective. -/
theorem exists_bijective_witness_assignment
    (hG : G.IsExtremal H.Free) (hF : F.IsExtremal H.Free) :
    ∃ f : addedEdges G F → removedEdges G F,
      Function.Bijective f ∧ ∀ a, Witness H G F a.1 (f a).1 := by
  classical
  obtain ⟨f, hf, hw⟩ := exists_injective_witness_assignment hG hF.1
  refine ⟨f, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, ?_⟩, hw⟩
  simpa only [Fintype.card_coe] using card_addedEdges_eq_card_removedEdges hG hF

/-- Equivalence form of the bijective witness assignment. -/
theorem exists_witness_equiv
    (hG : G.IsExtremal H.Free) (hF : F.IsExtremal H.Free) :
    ∃ f : addedEdges G F ≃ removedEdges G F,
      ∀ a, Witness H G F a.1 (f a).1 := by
  obtain ⟨f, hf, hw⟩ := exists_bijective_witness_assignment hG hF
  exact ⟨Equiv.ofBijective f hf, hw⟩

end Finite

end Erdos713Exchange
