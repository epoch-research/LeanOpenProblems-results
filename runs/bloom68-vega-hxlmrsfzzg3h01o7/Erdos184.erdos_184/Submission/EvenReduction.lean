import Submission.Infrastructure

/-!
# Reduction to finite even graphs

This file proves the parity-forest reduction for the exact decomposition predicate
in `Submission.Spec`.  An inclusion-minimal subgraph with the original degree
parities is a forest: deleting a cycle preserves all degree parities.  The forest
has at most `n - 1` edges, and its edge complement is even.

No linear bound for even graphs is asserted here.  Such a bound is a hypothesis
of the reduction, and neither admitted statement in `Submission.Spec` is used.
-/

open Filter SimpleGraph

namespace Erdos184.EvenReduction

open Infrastructure

universe u

variable {V : Type u} {G H : SimpleGraph V}

/-- Change the ambient graph of a subgraph without changing its vertices or edges. -/
def liftSubgraph (hHG : H ≤ G) (S : H.Subgraph) : G.Subgraph where
  verts := S.verts
  Adj := S.Adj
  adj_sub h := hHG (S.adj_sub h)
  edge_vert := S.edge_vert
  symm := S.symm

@[simp]
theorem liftSubgraph_verts (hHG : H ≤ G) (S : H.Subgraph) :
    (liftSubgraph hHG S).verts = S.verts := rfl

@[simp]
theorem liftSubgraph_coe (hHG : H ≤ G) (S : H.Subgraph) :
    (liftSubgraph hHG S).coe = S.coe := rfl

@[simp]
theorem liftSubgraph_edgeSet (hHG : H ≤ G) (S : H.Subgraph) :
    (liftSubgraph hHG S).edgeSet = S.edgeSet := rfl

/-- Changing the ambient graph does not identify distinct subgraphs. -/
theorem liftSubgraph_injective (hHG : H ≤ G) : Function.Injective (liftSubgraph hHG) := by
  intro S T h
  exact Subgraph.ext (congrArg (fun R : G.Subgraph => R.verts) h)
    (congrArg (fun R : G.Subgraph => R.Adj) h)

/-- Lift a finite family of pieces to a larger ambient graph. -/
noncomputable def liftPieces (hHG : H ≤ G) (D : Finset H.Subgraph) : Finset G.Subgraph := by
  classical
  exact D.image (liftSubgraph hHG)

@[simp]
theorem mem_liftPieces (hHG : H ≤ G) (D : Finset H.Subgraph) (S : G.Subgraph) :
    S ∈ liftPieces hHG D ↔ ∃ T ∈ D, liftSubgraph hHG T = S := by
  classical
  simp only [liftPieces, Finset.mem_image]

@[simp]
theorem liftPieces_card (hHG : H ≤ G) (D : Finset H.Subgraph) :
    (liftPieces hHG D).card = D.card := by
  classical
  exact Finset.card_image_of_injective D (liftSubgraph_injective hHG)

/-- Lifting preserves pairwise edge-disjointness. -/
theorem liftPieces_pairwiseDisjoint (hHG : H ≤ G) {D : Finset H.Subgraph}
    (hD : Set.PairwiseDisjoint (D : Set H.Subgraph) (fun S => S.edgeSet)) :
    Set.PairwiseDisjoint (liftPieces hHG D : Set G.Subgraph) (fun S => S.edgeSet) := by
  intro S hS T hT hST
  obtain ⟨S, hSD, rfl⟩ := (mem_liftPieces hHG D S).mp hS
  obtain ⟨T, hTD, rfl⟩ := (mem_liftPieces hHG D T).mp hT
  exact hD hSD hTD (fun h => hST (congrArg (liftSubgraph hHG) h))

/-- Lifting preserves the union of the edge sets exactly. -/
theorem liftPieces_edgeUnion (hHG : H ≤ G) (D : Finset H.Subgraph) :
    (⋃ S ∈ liftPieces hHG D, S.edgeSet) = ⋃ S ∈ D, S.edgeSet := by
  ext e
  simp only [Set.mem_iUnion, mem_liftPieces]
  constructor
  · rintro ⟨T, ⟨S, hS, rfl⟩, he⟩
    exact ⟨S, hS, he⟩
  · rintro ⟨S, hS, he⟩
    exact ⟨liftSubgraph hHG S, ⟨S, hS, rfl⟩, he⟩

open scoped Classical in
/-- Glue exact decompositions of two edge-disjoint spanning subgraphs. -/
theorem isDecomposition_union_liftPieces {A B : SimpleGraph V}
    (hAG : A ≤ G) (hBG : B ≤ G) (hdisj : Disjoint A B) (hcover : A ⊔ B = G)
    {DA : Finset A.Subgraph} {DB : Finset B.Subgraph}
    (hDA : IsDecomposition A DA) (hDB : IsDecomposition B DB) :
    IsDecomposition G (liftPieces hAG DA ∪ liftPieces hBG DB) := by
  classical
  constructor
  · rw [Finset.coe_union]
    refine (liftPieces_pairwiseDisjoint hAG hDA.1).union
      (liftPieces_pairwiseDisjoint hBG hDB.1) ?_
    intro S hS T hT _
    obtain ⟨S, _, rfl⟩ := (mem_liftPieces hAG DA S).mp hS
    obtain ⟨T, _, rfl⟩ := (mem_liftPieces hBG DB T).mp hT
    exact (disjoint_edgeSet.mpr hdisj).mono S.edgeSet_subset T.edgeSet_subset
  · change (⋃ S ∈ (↑(liftPieces hAG DA ∪ liftPieces hBG DB) : Set G.Subgraph),
      S.edgeSet) = G.edgeSet
    rw [Finset.coe_union, Set.biUnion_union]
    simp only [Finset.mem_coe]
    rw [liftPieces_edgeUnion, liftPieces_edgeUnion, hDA.2, hDB.2, ← edgeSet_sup, hcover]

section Finite

variable [Fintype V]

open scoped Classical in
/-- Degrees subtract when one deletes a spanning subgraph. -/
theorem degree_sdiff_of_le (hHG : H ≤ G) (v : V) :
    (G \ H).degree v = G.degree v - H.degree v := by
  classical
  have hsets : (G \ H).neighborFinset v = G.neighborFinset v \ H.neighborFinset v := by
    ext w
    simp only [mem_neighborFinset, Finset.mem_sdiff, sdiff_adj]
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (mem_neighborFinset G v w).mpr (hHG ((mem_neighborFinset H v w).mp hw))
  rw [SimpleGraph.degree, hsets, Finset.card_sdiff_of_subset hsub]
  rfl

open scoped Classical in
/-- Deleting an even spanning subgraph preserves degree parity. -/
theorem even_degree_sdiff_iff (hHG : H ≤ G) (v : V) (hH : Even (H.degree v)) :
    Even ((G \ H).degree v) ↔ Even (G.degree v) := by
  rw [degree_sdiff_of_le hHG, Nat.even_sub (degree_le_of_le hHG)]
  simp only [hH, iff_true]

open scoped Classical in
/-- A cycle, viewed on the full ambient vertex type, has even degree at every vertex. -/
theorem even_degree_cycle {v : V} {p : G.Walk v v} (hp : p.IsCycle) (w : V) :
    Even (p.toSubgraph.spanningCoe.degree w) := by
  classical
  rw [Subgraph.degree_spanningCoe]
  by_cases hw : w ∈ p.toSubgraph.verts
  · have hdeg : p.toSubgraph.degree w = 2 := by
      rw [Subgraph.degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hw)
    rw [hdeg]
    decide
  · rw [Subgraph.degree_of_notMem_verts hw]
    exact Even.zero

omit [Fintype V] in
/-- Deleting the edges of a cycle strictly decreases the ambient graph. -/
theorem sdiff_cycle_lt {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    G \ p.toSubgraph.spanningCoe < G := by
  refine lt_of_le_of_ne sdiff_le ?_
  intro heq
  have ha := p.toSubgraph_adj_snd hp.not_nil
  have hb : (G \ p.toSubgraph.spanningCoe).Adj v p.snd := by
    rw [heq]
    exact p.toSubgraph.adj_sub ha
  exact hb.2 ha

open scoped Classical in
/-- Every finite graph has an acyclic spanning subgraph with the same degree parities. -/
theorem exists_acyclic_same_parity (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      ∀ v, Even (F.degree v) ↔ Even (G.degree v) := by
  classical
  let S : Set (SimpleGraph V) := {F | ∀ v, Even (F.degree v) ↔ Even (G.degree v)}
  have hG : G ∈ S := fun _ => Iff.rfl
  obtain ⟨F, hFG, hmin⟩ := S.toFinite.exists_le_minimal hG
  refine ⟨F, hFG, ?_, hmin.prop⟩
  intro v p hp
  apply hmin.not_prop_of_lt (sdiff_cycle_lt hp)
  intro w
  convert (even_degree_sdiff_iff p.toSubgraph.spanningCoe_le w (even_degree_cycle hp w)).trans
    (hmin.prop w) using 1
  congr!

open scoped Classical in
/-- A forest on `n` vertices has at most `n - 1` edges (also for `n = 0`). -/
theorem card_edges_le_of_isAcyclic (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
    letI := hV
    have hbound := G.card_edgeFinset_le_card_choose_two
    simpa using hbound
  | inr hV =>
    letI := hV
    obtain ⟨T, hGT, hT⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
      (G := (⊤ : SimpleGraph V)) le_top hG
    have htree : T.IsTree :=
      (connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hT
    have hcard := htree.card_edgeFinset
    have hle := Finset.card_le_card (edgeFinset_mono hGT)
    omega

open scoped Classical in
/--
The parity forest: it has exactly the original odd-degree vertices, at most
`n - 1` edges, and deleting it leaves an even simple graph on the same vertices.
-/
theorem exists_parity_forest (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      (∀ v, Odd (F.degree v) ↔ Odd (G.degree v)) ∧
      F.edgeFinset.card ≤ Fintype.card V - 1 ∧
      ∀ v, Even ((G \ F).degree v) := by
  classical
  obtain ⟨F, hFG, hforest, hparity⟩ := exists_acyclic_same_parity G
  refine ⟨F, hFG, hforest, ?_, card_edges_le_of_isAcyclic hforest, ?_⟩
  · intro v
    simpa only [← Nat.not_even_iff_odd] using not_congr (hparity v)
  · intro v
    rw [degree_sdiff_of_le hFG, Nat.even_sub (degree_le_of_le hFG)]
    exact (hparity v).symm

open scoped Classical in
/-- The exact admissibility predicate is unchanged by lifting pieces. -/
theorem liftPieces_isCycleOrEdge (hHG : H ≤ G) {D : Finset H.Subgraph}
    (hD : ∀ S ∈ D, IsCycleOrEdge S.coe) :
    ∀ S ∈ liftPieces hHG D, IsCycleOrEdge S.coe := by
  intro S hS
  obtain ⟨T, hTD, rfl⟩ := (mem_liftPieces hHG D S).mp hS
  exact hD T hTD

open scoped Classical in
/-- Extend a decomposition of `G \ F` by one singleton piece for each edge of `F`. -/
theorem extend_decomposition {F : SimpleGraph V} (hFG : F ≤ G)
    {D : Finset (G \ F).Subgraph}
    (hpieces : ∀ S ∈ D, IsCycleOrEdge S.coe) (hD : IsDecomposition (G \ F) D) :
    ∃ D' : Finset G.Subgraph,
      (∀ S ∈ D', IsCycleOrEdge S.coe) ∧ IsDecomposition G D' ∧
      D'.card ≤ D.card + F.edgeFinset.card := by
  classical
  let D' := liftPieces (show G \ F ≤ G from sdiff_le) D ∪
    liftPieces hFG (singletonEdgeDecomposition F)
  refine ⟨D', ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact liftPieces_isCycleOrEdge sdiff_le hpieces S hS
    · exact liftPieces_isCycleOrEdge hFG singletonEdgeDecomposition_isCycleOrEdge S hS
  · exact isDecomposition_union_liftPieces sdiff_le hFG disjoint_sdiff_self_left
      (sdiff_sup_cancel hFG) hD singletonEdgeDecomposition_isDecomposition
  · calc
      D'.card ≤ (liftPieces (show G \ F ≤ G from sdiff_le) D).card +
          (liftPieces hFG (singletonEdgeDecomposition F)).card := Finset.card_union_le _ _
      _ = D.card + F.edgeFinset.card := by
        rw [liftPieces_card, liftPieces_card, singletonEdgeDecomposition_card]

open scoped Classical in
/--
The finite reduction, with the sharper additive cost `n - 1`: it suffices to
bound even graphs on the same vertex type.  No sign condition on `K` is needed.
-/
theorem decomposition_bound_of_even_bound (K : ℝ)
    (hEven : ∀ E : SimpleGraph V, (∀ v, Even (E.degree v)) →
      ∃ D : Finset E.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition E D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
      (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) + ((Fintype.card V - 1 : ℕ) : ℝ) := by
  classical
  obtain ⟨F, hFG, _, _, hcard, hrem⟩ := exists_parity_forest G
  obtain ⟨D, hpieces, hD, hbound⟩ := hEven (G \ F) (by
    intro v
    convert hrem v using 1
    congr!)
  obtain ⟨D', hpieces', hD', hcount⟩ := extend_decomposition hFG hpieces hD
  refine ⟨D', hpieces', hD', ?_⟩
  have hcount' : (D'.card : ℝ) ≤ (D.card : ℝ) + (F.edgeFinset.card : ℝ) := by
    exact_mod_cast hcount
  have hcard' : (F.edgeFinset.card : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

end Finite

open scoped Classical in
/--
A uniform `K * n` exact cycle/edge bound for finite even simple graphs implies a
uniform `(K + 1) * n` exact cycle/edge bound for all finite simple graphs.
-/
theorem uniform_linear_bound_of_even (K : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ (K + 1) * (Fintype.card V : ℝ) := by
  intro V _ _ G
  obtain ⟨D, hpieces, hD, hbound⟩ := decomposition_bound_of_even_bound K (hEven (V := V)) G
  refine ⟨D, hpieces, hD, ?_⟩
  have hn : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.sub_le (Fintype.card V) 1
  nlinarith

open scoped Classical in
/-- The original asymptotic target follows conditionally from the even-graph bound. -/
theorem asymptotic_of_even_linear_bound (K : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  exact asymptotic_of_uniform_linear_bound (K + 1) (uniform_linear_bound_of_even K hEven)

open scoped Classical in
/-- The reduction also applies to the stronger hypothesis of pure-cycle decompositions. -/
theorem uniform_linear_bound_of_even_cycles (K : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ (K + 1) * (Fintype.card V : ℝ) := by
  apply uniform_linear_bound_of_even K
  intro V _ _ G hG
  obtain ⟨D, hpieces, hD, hbound⟩ := hEven G hG
  refine ⟨D, ?_, hD, hbound⟩
  intro S hS
  apply Or.inl
  convert hpieces S hS using 1
  congr!

open scoped Classical in
/-- The exact asymptotic target under a hypothetical linear pure-cycle bound for even graphs. -/
theorem asymptotic_of_even_cycle_bound (K : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  exact asymptotic_of_uniform_linear_bound (K + 1)
    (uniform_linear_bound_of_even_cycles K hEven)

end Erdos184.EvenReduction
