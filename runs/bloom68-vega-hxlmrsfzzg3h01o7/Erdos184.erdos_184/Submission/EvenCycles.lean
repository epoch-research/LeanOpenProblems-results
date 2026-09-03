import Submission.UniformEquivalence

/-!
# Pure-cycle decompositions of finite even graphs

Every finite simple graph with even degrees has an exact decomposition into
connected, 2-regular subgraphs. Deleting a cyclic walk preserves even degrees;
the acyclic base case is empty by the leaf lemma for a nontrivial tree component.
Each deleted cycle has at least three edges, giving at most `|E| / 3` pieces.

For even graphs, any exact cycle-or-edge decomposition can be replaced by an exact
pure-cycle decomposition without increasing its cardinality, retaining every old
pure-cycle piece. Thus the two uniform-bound hypotheses are equivalent for each
fixed constant. Existence of such a nonnegative constant is equivalent to the
existing asymptotic target.

The unconditional bound here is in terms of the number of **edges**, not a
uniform linear bound in the number of vertices. No such linear bound is asserted.
-/

open SimpleGraph

namespace Erdos184.EvenCycles

open Infrastructure EvenReduction

universe u

section Finite

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
/-- A finite acyclic graph with even degrees has no edges. Isolated vertices are allowed. -/
theorem eq_bot_of_even_isAcyclic (hG : ∀ v, Even (G.degree v)) (hforest : G.IsAcyclic) :
    G = ⊥ := by
  classical
  apply bot_unique
  intro v w hvw
  let C := G.connectedComponentMk v
  have hv : v ∈ C.supp := rfl
  have hw : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hv hvw
  letI : Nontrivial C := ⟨⟨⟨v, hv⟩, ⟨w, hw⟩, fun h => hvw.ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨x, hx⟩ := (hforest.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  have hdeg : C.toSimpleGraph.degree x = G.degree x := by
    convert degree_induce_of_neighborSet_subset
      (G := G) (s := C.supp) (v := x)
      (fun y hy => C.mem_supp_of_adj_mem_supp x.property hy) using 1
    congr!
  have heven := hG x
  rw [← hdeg, hx] at heven
  exact (by decide : ¬Even (1 : ℕ)) heven

open scoped Classical in
/-- A cyclic walk gives a pure cycle on precisely its own vertices. -/
theorem pureCycle_toSubgraph {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.toSubgraph.coe.Connected ∧ p.toSubgraph.coe.IsRegularOfDegree 2 := by
  classical
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  intro w
  rw [Subgraph.coe_degree, Subgraph.degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp w.property)

open scoped Classical in
/-- A trail's spanning subgraph has as many edges as the trail has steps. -/
theorem card_edges_toSubgraph_of_isTrail {v w : V} {p : G.Walk v w} (hp : p.IsTrail) :
    p.toSubgraph.spanningCoe.edgeFinset.card = p.length := by
  classical
  have hedges : p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [mem_edgeFinset, List.mem_toFinset]
    exact p.mem_edges_toSubgraph
  rw [hedges, List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges]

omit [Fintype V] in
open scoped Classical in
/-- Restoring one piece after deleting exactly its edges preserves the exact decomposition. -/
theorem isDecomposition_insert_liftPieces (S : G.Subgraph)
    {D : Finset (G \ S.spanningCoe).Subgraph} (hD : IsDecomposition (G \ S.spanningCoe) D) :
    IsDecomposition G (insert S (liftPieces (show G \ S.spanningCoe ≤ G from sdiff_le) D)) := by
  classical
  constructor
  · rw [Finset.coe_insert]
    apply (liftPieces_pairwiseDisjoint sdiff_le hD.1).insert
    intro T hT _
    obtain ⟨T, _, rfl⟩ := (mem_liftPieces sdiff_le D T).mp hT
    exact (disjoint_edgeSet.mpr
      (show Disjoint S.spanningCoe (G \ S.spanningCoe) from disjoint_sdiff_self_right)).mono
      (by intro e he; exact he) T.edgeSet_subset
  · change (⋃ T ∈ (↑(insert S (liftPieces (show G \ S.spanningCoe ≤ G from sdiff_le) D)) :
        Set G.Subgraph), T.edgeSet) = G.edgeSet
    rw [Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_coe]
    rw [liftPieces_edgeUnion, hD.2]
    change S.spanningCoe.edgeSet ∪ (G \ S.spanningCoe).edgeSet = G.edgeSet
    rw [← edgeSet_sup, sup_sdiff_cancel_right S.spanningCoe_le]

open scoped Classical in
/-- Every finite even graph has an exact pure-cycle decomposition with at most `|E| / 3` pieces. -/
theorem exists_pureCycle_decomposition (G : SimpleGraph V) (hG : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ G.edgeFinset.card / 3 := by
  classical
  revert hG
  induction G using WellFoundedLT.induction with
  | ind G ih =>
    intro hG
    by_cases hforest : G.IsAcyclic
    · have hbot := eq_bot_of_even_isAcyclic hG hforest
      subst G
      refine ⟨∅, by simp, ?_, by simp⟩
      constructor <;> simp [Set.PairwiseDisjoint]
    · obtain ⟨v, p, hp⟩ : ∃ v, ∃ p : G.Walk v v, p.IsCycle := by
        simpa only [SimpleGraph.IsAcyclic, not_forall, Classical.not_not] using hforest
      have heven : ∀ w, Even ((G \ p.toSubgraph.spanningCoe).degree w) := by
        intro w
        exact (even_degree_sdiff_iff p.toSubgraph.spanningCoe_le w (even_degree_cycle hp w)).mpr
          (hG w)
      obtain ⟨D, hpieces, hD, hcount⟩ := ih (G \ p.toSubgraph.spanningCoe) (sdiff_cycle_lt hp) (by
        intro w
        convert heven w using 1
        congr!)
      have hcount' : D.card ≤ (G \ p.toSubgraph.spanningCoe).edgeFinset.card / 3 := by
        convert hcount using 1
        congr!
      let D' := insert p.toSubgraph (liftPieces (show G \ p.toSubgraph.spanningCoe ≤ G from sdiff_le) D)
      refine ⟨D', ?_, isDecomposition_insert_liftPieces _ hD, ?_⟩
      · intro S hS
        rcases Finset.mem_insert.mp hS with rfl | hS
        · exact pureCycle_toSubgraph hp
        · obtain ⟨T, hT, rfl⟩ := (mem_liftPieces sdiff_le D S).mp hS
          constructor
          · exact (hpieces T hT).1
          · convert (hpieces T hT).2 using 1
      · have hcard : D'.card ≤ D.card + 1 := by
          simpa only [liftPieces_card] using Finset.card_insert_le p.toSubgraph
            (liftPieces (show G \ p.toSubgraph.spanningCoe ≤ G from sdiff_le) D)
        have hsum : (G \ p.toSubgraph.spanningCoe).edgeFinset.card +
            p.toSubgraph.spanningCoe.edgeFinset.card = G.edgeFinset.card := by
          rw [edgeFinset_sdiff]
          exact Finset.card_sdiff_add_card_eq_card (edgeFinset_mono p.toSubgraph.spanningCoe_le)
        have hthree : 3 ≤ p.toSubgraph.spanningCoe.edgeFinset.card := by
          rw [card_edges_toSubgraph_of_isTrail hp.isTrail]
          exact hp.three_le_length
        omega

open scoped Classical in
/-- The weaker edge-count bound, useful when replacing singleton-edge pieces. -/
theorem exists_pureCycle_decomposition_card_le_edges (G : SimpleGraph V)
    (hG : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ G.edgeFinset.card := by
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_pureCycle_decomposition G hG
  exact ⟨D, hpieces, hD, hcard.trans (Nat.div_le_self _ _)⟩

/- ## Unions of pieces and replacement of singleton edges -/

/-- The spanning graph whose edges are those in a finite family of subgraphs. -/
def piecesGraph (D : Finset G.Subgraph) : SimpleGraph V :=
  D.sup (fun S => S.spanningCoe)

omit [Fintype V] in
/-- The union of pieces is still a spanning subgraph of the ambient graph. -/
theorem piecesGraph_le (D : Finset G.Subgraph) : piecesGraph D ≤ G :=
  Finset.sup_le (fun S _ => S.spanningCoe_le)

omit [Fintype V] in
/-- The spanning union has exactly the union of the original edge sets. -/
theorem piecesGraph_edgeSet (D : Finset G.Subgraph) :
    (piecesGraph D).edgeSet = ⋃ S ∈ D, S.edgeSet := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [piecesGraph]
  | @insert S D hS ih =>
    simp only [piecesGraph, Finset.sup_insert, edgeSet_sup] at ih ⊢
    rw [ih]
    change S.edgeSet ∪ (⋃ T ∈ D, T.edgeSet) = ⋃ T ∈ insert S D, T.edgeSet
    simp

omit [Fintype V] in
/-- For an exact decomposition the spanning union is the original graph. -/
theorem piecesGraph_eq_of_isDecomposition {D : Finset G.Subgraph} (hD : IsDecomposition G D) :
    piecesGraph D = G := by
  apply edgeSet_inj.mp
  rw [piecesGraph_edgeSet, hD.2]

open scoped Classical in
/-- Degrees add under edge-disjoint union, even when vertices overlap. -/
theorem degree_sup_of_disjoint {A B : SimpleGraph V} (hAB : Disjoint A B) (v : V) :
    (A ⊔ B).degree v = A.degree v + B.degree v := by
  classical
  have hsets : (A ⊔ B).neighborFinset v = A.neighborFinset v ∪ B.neighborFinset v := by
    ext w
    simp
  have hdisj : Disjoint (A.neighborFinset v) (B.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    exact Set.disjoint_left.mp (disjoint_edgeSet.mpr hAB)
      (show s(v, w) ∈ A.edgeSet from (mem_neighborFinset A v w).mp hwA)
      (show s(v, w) ∈ B.edgeSet from (mem_neighborFinset B v w).mp hwB)
  rw [← card_neighborFinset_eq_degree, hsets, Finset.card_union_of_disjoint hdisj,
    card_neighborFinset_eq_degree, card_neighborFinset_eq_degree]

open scoped Classical in
/-- A 2-regular piece has even spanning degrees, including degree zero off its vertices. -/
theorem even_degree_spanningCoe_of_regular (S : G.Subgraph) (hS : S.coe.IsRegularOfDegree 2)
    (v : V) : Even (S.spanningCoe.degree v) := by
  classical
  rw [Subgraph.degree_spanningCoe]
  by_cases hv : v ∈ S.verts
  · have hdeg : S.degree v = 2 := by
      simpa only [Subgraph.coe_degree] using hS ⟨v, hv⟩
    rw [hdeg]
    decide
  · rw [Subgraph.degree_of_notMem_verts hv]
    exact Even.zero

open scoped Classical in
/-- An edge-disjoint union of even pieces is even. -/
theorem even_degree_piecesGraph {D : Finset G.Subgraph}
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun S => S.edgeSet))
    (heven : ∀ S ∈ D, ∀ v, Even (S.spanningCoe.degree v)) (v : V) :
    Even ((piecesGraph D).degree v) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [piecesGraph, SimpleGraph.degree, SimpleGraph.neighborFinset]
  | @insert S D hS ih =>
    have hdisjD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun T => T.edgeSet) :=
      hdisj.subset (by simp)
    have hSD : Disjoint S.spanningCoe (piecesGraph D) := by
      apply Finset.disjoint_sup_right.mpr
      intro T hT
      apply disjoint_edgeSet.mp
      exact hdisj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hT)
        (fun h => hS (h ▸ hT))
    have hdeg : (piecesGraph (insert S D)).degree v =
        S.spanningCoe.degree v + (piecesGraph D).degree v := by
      convert degree_sup_of_disjoint hSD v using 1
      simp [piecesGraph, SimpleGraph.degree, SimpleGraph.neighborFinset]
    rw [hdeg]
    exact (heven S (Finset.mem_insert_self _ _) v).add
      (ih hdisjD (fun T hT => heven T (Finset.mem_insert_of_mem hT)))

open scoped Classical in
/-- Edge count of a union is at most the sum of the edge counts of its pieces. -/
theorem card_edges_piecesGraph_le (D : Finset G.Subgraph) :
    (piecesGraph D).edgeFinset.card ≤ ∑ S ∈ D, S.coe.edgeFinset.card := by
  classical
  have hcard : (piecesGraph D).edgeFinset.card = (piecesGraph D).edgeSet.ncard :=
    (Set.ncard_eq_toFinset_card' _).symm
  rw [hcard, piecesGraph_edgeSet]
  simpa only [coe_edgeFinset_card] using D.set_ncard_biUnion_le (fun S => S.edgeSet)

omit [Fintype V] in
open scoped Classical in
/-- Glue a family already in `G` to a decomposition of its edge complement. -/
theorem isDecomposition_union_complement {C : Finset G.Subgraph}
    (hC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun S => S.edgeSet))
    {D : Finset (G \ piecesGraph C).Subgraph} (hD : IsDecomposition (G \ piecesGraph C) D) :
    IsDecomposition G (C ∪ liftPieces (show G \ piecesGraph C ≤ G from sdiff_le) D) := by
  classical
  constructor
  · rw [Finset.coe_union]
    refine hC.union (liftPieces_pairwiseDisjoint sdiff_le hD.1) ?_
    intro S hS T hT _
    obtain ⟨T, _, rfl⟩ := (mem_liftPieces sdiff_le D T).mp hT
    apply (disjoint_edgeSet.mpr
      (show Disjoint (piecesGraph C) (G \ piecesGraph C) from disjoint_sdiff_self_right)).mono
    · intro e he
      rw [piecesGraph_edgeSet]
      exact Set.mem_iUnion₂_of_mem hS he
    · exact T.edgeSet_subset
  · change (⋃ S ∈ (↑(C ∪ liftPieces (show G \ piecesGraph C ≤ G from sdiff_le) D) :
        Set G.Subgraph), S.edgeSet) = G.edgeSet
    rw [Finset.coe_union, Set.biUnion_union]
    simp only [Finset.mem_coe]
    rw [← piecesGraph_edgeSet, liftPieces_edgeUnion, hD.2, ← edgeSet_sup,
      sup_sdiff_cancel_right (piecesGraph_le C)]

open scoped Classical in
/-- Lifting a family of pure cycles does not change its admissibility. -/
theorem liftPieces_pureCycle {H : SimpleGraph V} (hHG : H ≤ G) {D : Finset H.Subgraph}
    (hD : ∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) :
    ∀ S ∈ liftPieces hHG D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2 := by
  intro S hS
  obtain ⟨T, hT, rfl⟩ := (mem_liftPieces hHG D S).mp hS
  constructor
  · exact (hD T hT).1
  · convert (hD T hT).2 using 1

omit [Fintype V] in
open scoped Classical in
/-- Deleting a subfamily of an exact decomposition leaves exactly the edges in the other pieces. -/
theorem complement_piecesGraph_eq {C D : Finset G.Subgraph}
    (hD : IsDecomposition G D) (hCD : C ⊆ D) :
    G \ piecesGraph C = piecesGraph (D \ C) := by
  classical
  apply edgeSet_inj.mp
  rw [edgeSet_sdiff, piecesGraph_edgeSet, piecesGraph_edgeSet]
  ext e
  simp only [Set.mem_diff, Set.mem_iUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨heG, heC⟩
    rw [← hD.2] at heG
    simp only [Set.mem_iUnion] at heG
    obtain ⟨S, hSD, heS⟩ := heG
    exact ⟨S, ⟨hSD, fun hSC => heC ⟨S, hSC, heS⟩⟩, heS⟩
  · rintro ⟨S, ⟨hSD, hSC⟩, heS⟩
    refine ⟨S.edgeSet_subset heS, ?_⟩
    rintro ⟨T, hTC, heT⟩
    exact Set.disjoint_left.mp (hD.1 hSD (hCD hTC) (fun h => hSC (h ▸ hTC))) heS heT

open scoped Classical in
/-- Exact pure-cycle decomposability characterizes even degree for finite simple graphs. -/
theorem even_iff_exists_pureCycle_decomposition (G : SimpleGraph V) :
    (∀ v, Even (G.degree v)) ↔
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D := by
  classical
  constructor
  · intro hG
    obtain ⟨D, hpieces, hD, _⟩ := exists_pureCycle_decomposition G hG
    exact ⟨D, hpieces, hD⟩
  · rintro ⟨D, hpieces, hD⟩ v
    have heven := even_degree_piecesGraph hD.1
      (fun S hS => even_degree_spanningCoe_of_regular S (hpieces S hS).2) v
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      piecesGraph_eq_of_isDecomposition hD] using heven

open scoped Classical in
/--
In a finite even graph, replace the singleton-edge pieces of any exact cycle-or-edge
partition by pure cycles, without increasing the number of pieces. The old pure cycles
are retained. Singleton-edge pieces may carry isolated vertices; only their edges matter.
-/
theorem purify_decomposition (hG : ∀ v, Even (G.degree v)) {D : Finset G.Subgraph}
    (hpieces : ∀ S ∈ D, IsCycleOrEdge S.coe) (hD : IsDecomposition G D) :
    ∃ D' : Finset G.Subgraph,
      (∀ S ∈ D', S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D' ∧ D'.card ≤ D.card ∧
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2 → S ∈ D') := by
  classical
  let C := D.filter (fun S => S.coe.Connected ∧ S.coe.IsRegularOfDegree 2)
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hC : ∀ S ∈ C, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2 := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hCdisj : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun S => S.edgeSet) :=
    hD.1.subset hCD
  have hevenC : ∀ v, Even ((piecesGraph C).degree v) :=
    even_degree_piecesGraph hCdisj
      (fun S hS => even_degree_spanningCoe_of_regular S (hC S hS).2)
  have hsingle : ∀ S ∈ D \ C, S.coe.edgeFinset.card = 1 := by
    intro S hS
    obtain ⟨hSD, hSC⟩ := Finset.mem_sdiff.mp hS
    rcases hpieces S hSD with hpure | hedge
    · apply (hSC ?_).elim
      apply Finset.mem_filter.mpr
      refine ⟨hSD, hpure.1, ?_⟩
      convert hpure.2 using 1
    · exact hedge
  have hRcard : (G \ piecesGraph C).edgeFinset.card ≤ (D \ C).card := by
    have hsum : (∑ S ∈ D \ C, S.coe.edgeFinset.card) = (D \ C).card := by
      simpa using Finset.sum_const_nat hsingle
    have hcount := card_edges_piecesGraph_le (D \ C)
    rw [hsum] at hcount
    simpa only [SimpleGraph.edgeFinset, complement_piecesGraph_eq hD hCD] using hcount
  obtain ⟨P, hP, hdecompP, hcardP⟩ := exists_pureCycle_decomposition_card_le_edges
    (G \ piecesGraph C) (by
      intro v
      convert (even_degree_sdiff_iff (piecesGraph_le C) v (hevenC v)).mpr (hG v) using 1
      congr!)
  let D' := C ∪ liftPieces (show G \ piecesGraph C ≤ G from sdiff_le) P
  refine ⟨D', ?_, isDecomposition_union_complement hCdisj hdecompP, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hC S hS
    · exact liftPieces_pureCycle sdiff_le hP S hS
  · have hcardP' : P.card ≤ (G \ piecesGraph C).edgeFinset.card := by
      convert hcardP using 1
      congr!
    calc
      D'.card ≤ C.card + (liftPieces (show G \ piecesGraph C ≤ G from sdiff_le) P).card :=
        Finset.card_union_le _ _
      _ = C.card + P.card := by rw [liftPieces_card]
      _ ≤ C.card + (D \ C).card := Nat.add_le_add_left (hcardP'.trans hRcard) _
      _ = D.card := by simpa [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hCD
  · intro S hSD hpure
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSD, hpure⟩)

end Finite

/- ## Conditional uniform-bound equivalences -/

open scoped Classical in
/-- A hypothetical uniform linear pure-cycle bound, restricted to finite even graphs. -/
def UniformEvenPureCycleBound (K : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  (∀ v, Even (G.degree v)) →
  ∃ D : Finset G.Subgraph,
    (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)

/--
For each fixed real `K`, the even cycle-or-edge bound is equivalent to the even
pure-cycle bound with the **same** `K`. This is an equivalence, not an existence claim.
-/
theorem uniform_even_linear_bound_iff_pureCycle_bound (K : ℝ) :
    UniformEquivalence.UniformEvenLinearBound.{u} K ↔ UniformEvenPureCycleBound.{u} K := by
  classical
  constructor
  · intro h V _ _ G hG
    obtain ⟨D, hpieces, hD, hcard⟩ := h G hG
    obtain ⟨D', hpieces', hD', hcount, _⟩ := purify_decomposition hG hpieces hD
    refine ⟨D', hpieces', hD', ?_⟩
    have hcount' : (D'.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hcount
    exact hcount'.trans hcard
  · intro h V _ _ G hG
    obtain ⟨D, hpieces, hD, hcard⟩ := h G hG
    refine ⟨D, ?_, hD, hcard⟩
    intro S hS
    apply Or.inl
    refine ⟨(hpieces S hS).1, ?_⟩
    convert (hpieces S hS).2 using 1

/-- The exact asymptotic proposition is equivalent to existence of a uniform even pure-cycle bound. -/
theorem asymptotic_iff_uniform_even_pureCycle_bound :
    UniformEquivalence.ExactTarget.{u} ↔
      ∃ K : ℝ, 0 ≤ K ∧ UniformEvenPureCycleBound.{u} K := by
  rw [UniformEquivalence.asymptotic_iff_uniform_even_linear_bound]
  exact exists_congr (fun K => and_congr_right
    (fun _ => uniform_even_linear_bound_iff_pureCycle_bound K))

/-- The all-graph cycle-or-edge uniform-bound conjecture has an equivalent even pure-cycle form. -/
theorem uniform_linear_bound_iff_uniform_even_pureCycle_bound :
    (∃ K : ℝ, 0 ≤ K ∧ UniformEquivalence.UniformLinearBound.{u} K) ↔
      ∃ K : ℝ, 0 ≤ K ∧ UniformEvenPureCycleBound.{u} K :=
  UniformEquivalence.asymptotic_iff_uniform_linear_bound.symm.trans
    asymptotic_iff_uniform_even_pureCycle_bound

end Erdos184.EvenCycles
