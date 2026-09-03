import Submission.EvenCycles

/-!
# Optimal pure-cycle partitions and a conditional OC reduction

This is supporting infrastructure, not a linear-bound proof. A pure cycle means
exactly a connected, 2-regular subgraph on its own vertices, and partitions use
`IsDecomposition` without changing its edge-disjoint-cover requirement.

The minimum number of cycles is defined using the existing finite-family
existence theorem. Subfamilies of a minimum partition are minimum on their
spanning edge unions. Gluing gives subadditivity and a one-cycle extension bound.

The OC property says that every pure cycle occurs in some minimum partition.
Strong edge induction reduces any monotone count-bound cost to graphs with OC.
In particular a hypothetical OC bound `K * |V|` suffices on the SAME ambient
vertex type, including all isolated vertices. No graphic-rank or connectedness
claim, and no unconditional linear bound, is made here.
-/

open SimpleGraph

namespace Erdos184.OptimalCycles

open Infrastructure EvenReduction EvenCycles
open scoped Classical

universe u

variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

/-- Evenness is on the full ambient vertex type; isolated vertices are retained. -/
def IsEven (G : SimpleGraph V) : Prop := ∀ v, Even (G.degree v)

/-- The pure-cycle branch of the original admissibility predicate. -/
def IsPureCycle (S : G.Subgraph) : Prop :=
  S.coe.Connected ∧ S.coe.IsRegularOfDegree 2

/-- A pure cycle satisfies the exact original cycle-or-edge admissibility predicate. -/
theorem IsPureCycle.isCycleOrEdge {S : G.Subgraph} (hS : IsPureCycle S) :
    IsCycleOrEdge S.coe := by
  refine Or.inl ⟨hS.1, ?_⟩
  convert hS.2 using 1

/-- An exact finite partition into pure cycles (not singleton edges). -/
def IsPureDecomposition (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  (∀ S ∈ D, IsPureCycle S) ∧ IsDecomposition G D

/-- Pure-cycle partitions exist for every finite even graph. -/
theorem exists_pureDecomposition (G : SimpleGraph V) (hG : IsEven G) :
    ∃ D : Finset G.Subgraph, IsPureDecomposition G D := by
  obtain ⟨D, hD, hcover, _⟩ := exists_pureCycle_decomposition G hG
  exact ⟨D, hD, hcover⟩

/-- A natural-number witness for defining the minimum by `Nat.find`. -/
theorem exists_cycleCount (G : SimpleGraph V) (hG : IsEven G) :
    ∃ n : ℕ, ∃ D : Finset G.Subgraph, IsPureDecomposition G D ∧ D.card = n := by
  obtain ⟨D, hD⟩ := exists_pureDecomposition G hG
  exact ⟨D.card, D, hD, rfl⟩

/-- The least size of an exact pure-cycle partition of a finite even graph. -/
noncomputable def minCycleCount (G : SimpleGraph V) (hG : IsEven G) : ℕ :=
  Nat.find (exists_cycleCount G hG)

/-- Optimality refers to the original pieces, not just isomorphism classes. -/
def IsOptimal (hG : IsEven G) (D : Finset G.Subgraph) : Prop :=
  IsPureDecomposition G D ∧ D.card = minCycleCount G hG

/-- The minimum is attained by an actual finite family of original subgraphs. -/
theorem exists_optimal (G : SimpleGraph V) (hG : IsEven G) :
    ∃ D : Finset G.Subgraph, IsOptimal hG D :=
  Nat.find_spec (exists_cycleCount G hG)

/-- The minimum is no larger than the size of any pure-cycle partition. -/
theorem minCycleCount_le_card (hG : IsEven G) {D : Finset G.Subgraph}
    (hD : IsPureDecomposition G D) : minCycleCount G hG ≤ D.card :=
  Nat.find_min' (exists_cycleCount G hG) ⟨D, hD, rfl⟩

/-- The attained minimum also has the existing edge-count upper bound. -/
theorem minCycleCount_le_edges_div_three (hG : IsEven G) :
    minCycleCount G hG ≤ G.edgeFinset.card / 3 := by
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_pureCycle_decomposition G hG
  exact (minCycleCount_le_card hG ⟨hpieces, hD⟩).trans hcard

/-- The edgeless graph is even at every ambient order, including zero. -/
theorem even_bot : IsEven (⊥ : SimpleGraph V) := by
  intro v
  have hv : Even ((⊥ : SimpleGraph V).degree v) := by simp
  convert hv using 1
  congr!

/-- The empty family is the exact pure-cycle partition of an edgeless graph. -/
theorem pureDecomposition_empty :
    IsPureDecomposition (⊥ : SimpleGraph V) ∅ := by
  constructor
  · simp
  · constructor <;> simp [Set.PairwiseDisjoint]

@[simp]
theorem minCycleCount_bot : minCycleCount (⊥ : SimpleGraph V) even_bot = 0 :=
  Nat.eq_zero_of_le_zero (minCycleCount_le_card even_bot pureDecomposition_empty)

/-- Zero cycles occur precisely when there are no edges; vertices need not be absent. -/
theorem minCycleCount_eq_zero_iff (hG : IsEven G) :
    minCycleCount G hG = 0 ↔ G = ⊥ := by
  constructor
  · intro hzero
    obtain ⟨D, hD, hcard⟩ := exists_optimal G hG
    have hDzero : D = ∅ := Finset.card_eq_zero.mp (hcard.trans hzero)
    have hcover := hD.2.2
    rw [hDzero] at hcover
    apply edgeSet_inj.mp
    simpa using hcover.symm
  · rintro rfl
    exact minCycleCount_bot

/-- Pure-cycle partitions force even degrees. -/
theorem IsPureDecomposition.isEven {D : Finset G.Subgraph}
    (hD : IsPureDecomposition G D) : IsEven G :=
  (even_iff_exists_pureCycle_decomposition G).mpr ⟨D, hD.1, hD.2⟩

/-- Every pure cycle has an edge, so an empty piece can never be a cycle. -/
theorem IsPureCycle.exists_adj {S : G.Subgraph} (hS : IsPureCycle S) :
    ∃ v w, S.Adj v w := by
  obtain ⟨v⟩ := hS.1.nonempty
  have hpos : 0 < S.coe.degree v := by rw [hS.2 v]; omega
  obtain ⟨w, hw⟩ := (S.coe.degree_pos_iff_exists_adj v).mp hpos
  exact ⟨v, w, hw⟩

/-- Deleting any pure-cycle piece strictly decreases the edge set. -/
theorem sdiff_pureCycle_lt (S : G.Subgraph) (hS : IsPureCycle S) :
    G \ S.spanningCoe < G := by
  refine lt_of_le_of_ne sdiff_le ?_
  intro heq
  obtain ⟨v, w, hvw⟩ := hS.exists_adj
  have hrem : (G \ S.spanningCoe).Adj v w := by
    rw [heq]
    exact S.adj_sub hvw
  exact hrem.2 hvw

/-- Deleting a pure cycle preserves evenness, on the unchanged vertex type. -/
theorem even_sdiff_pureCycle (hG : IsEven G) (S : G.Subgraph) (hS : IsPureCycle S) :
    IsEven (G \ S.spanningCoe) := by
  intro v
  convert (even_degree_sdiff_iff S.spanningCoe_le v
    (even_degree_spanningCoe_of_regular S hS.2 v)).mpr (hG v) using 1
  congr!

/-- Pure-cycle subfamilies have even spanning edge unions. -/
theorem even_piecesGraph {D : Finset G.Subgraph}
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun S => S.edgeSet))
    (hpieces : ∀ S ∈ D, IsPureCycle S) : IsEven (piecesGraph D) :=
  even_degree_piecesGraph hdisj
    (fun S hS => even_degree_spanningCoe_of_regular S (hpieces S hS).2)

/- ## Moving a subfamily to its own spanning edge union -/

/-- Change only the ambient graph of a piece whose edges lie in `H`. -/
def rebaseSubgraph (S : G.Subgraph) (hS : S.spanningCoe ≤ H) : H.Subgraph where
  verts := S.verts
  Adj := S.Adj
  adj_sub := fun h => hS h
  edge_vert := S.edge_vert
  symm := S.symm

omit [Fintype V] in
@[simp]
theorem rebaseSubgraph_coe (S : G.Subgraph) (hS : S.spanningCoe ≤ H) :
    (rebaseSubgraph S hS).coe = S.coe := rfl

omit [Fintype V] in
@[simp]
theorem rebaseSubgraph_edgeSet (S : G.Subgraph) (hS : S.spanningCoe ≤ H) :
    (rebaseSubgraph S hS).edgeSet = S.edgeSet := rfl

/-- A piece of a family, reinterpreted in its spanning union. -/
def pieceOnUnion (D : Finset G.Subgraph) (S : {S // S ∈ D}) :
    (piecesGraph D).Subgraph := rebaseSubgraph S.1 (Finset.le_sup S.2)

omit [Fintype V] in
/-- Reinterpretation retains the exact original vertices and edges. -/
@[simp]
theorem lift_pieceOnUnion (D : Finset G.Subgraph) (S : {S // S ∈ D}) :
    liftSubgraph (piecesGraph_le D) (pieceOnUnion D S) = S.1 := rfl

omit [Fintype V] in
/-- Different original pieces stay different in the union graph. -/
theorem pieceOnUnion_injective (D : Finset G.Subgraph) :
    Function.Injective (pieceOnUnion D) := by
  intro S T h
  apply Subtype.ext
  simpa only [lift_pieceOnUnion] using congrArg (liftSubgraph (piecesGraph_le D)) h

/-- The same finite family, with ambient graph changed to its own spanning union. -/
noncomputable def piecesOnUnion (D : Finset G.Subgraph) : Finset (piecesGraph D).Subgraph :=
  D.attach.image (pieceOnUnion D)

omit [Fintype V] in
@[simp]
theorem piecesOnUnion_card (D : Finset G.Subgraph) : (piecesOnUnion D).card = D.card := by
  rw [piecesOnUnion, Finset.card_image_of_injective _ (pieceOnUnion_injective D),
    Finset.card_attach]

omit [Fintype V] in
/-- Lifting the reinterpreted family recovers exactly the original family. -/
@[simp]
theorem liftPieces_piecesOnUnion (D : Finset G.Subgraph) :
    liftPieces (piecesGraph_le D) (piecesOnUnion D) = D := by
  ext S
  simp [liftPieces, piecesOnUnion, Finset.mem_attach]

set_option maxHeartbeats 800000 in
/-- Pairwise edge-disjoint pure cycles partition their own spanning edge union. -/
theorem pureDecomposition_piecesOnUnion {D : Finset G.Subgraph}
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun S => S.edgeSet))
    (hpieces : ∀ S ∈ D, IsPureCycle S) :
    IsPureDecomposition (piecesGraph D) (piecesOnUnion D) := by
  constructor
  · intro S hS
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS
    refine ⟨(hpieces T.1 T.2).1, ?_⟩
    convert (hpieces T.1 T.2).2 using 1
  · constructor
    · intro S hS T hT hne
      obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hT
      exact hdisj S.2 T.2 (fun h => hne (congrArg (pieceOnUnion D) (Subtype.ext h)))
    · rw [← liftPieces_edgeUnion (piecesGraph_le D), liftPieces_piecesOnUnion,
        piecesGraph_edgeSet]

/- ## Gluing and hereditary optimality -/

/-- Glue pure-cycle partitions of two edge-disjoint spanning subgraphs. -/
theorem pureDecomposition_union_liftPieces {A B : SimpleGraph V}
    (hAG : A ≤ G) (hBG : B ≤ G) (hdisj : Disjoint A B) (hcover : A ⊔ B = G)
    {DA : Finset A.Subgraph} {DB : Finset B.Subgraph}
    (hDA : IsPureDecomposition A DA) (hDB : IsPureDecomposition B DB) :
    IsPureDecomposition G (liftPieces hAG DA ∪ liftPieces hBG DB) := by
  refine ⟨?_, isDecomposition_union_liftPieces hAG hBG hdisj hcover hDA.2 hDB.2⟩
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · exact liftPieces_pureCycle hAG hDA.1 S hS
  · exact liftPieces_pureCycle hBG hDB.1 S hS

/-- Basic subadditivity for any edge-disjoint spanning cover. -/
theorem minCycleCount_le_add {A B : SimpleGraph V}
    (hG : IsEven G) (hA : IsEven A) (hB : IsEven B)
    (hAG : A ≤ G) (hBG : B ≤ G) (hdisj : Disjoint A B) (hcover : A ⊔ B = G) :
    minCycleCount G hG ≤ minCycleCount A hA + minCycleCount B hB := by
  obtain ⟨DA, hDA, hcardA⟩ := exists_optimal A hA
  obtain ⟨DB, hDB, hcardB⟩ := exists_optimal B hB
  calc
    minCycleCount G hG ≤ (liftPieces hAG DA ∪ liftPieces hBG DB).card :=
      minCycleCount_le_card hG
        (pureDecomposition_union_liftPieces hAG hBG hdisj hcover hDA hDB)
    _ ≤ (liftPieces hAG DA).card + (liftPieces hBG DB).card := Finset.card_union_le _ _
    _ = minCycleCount A hA + minCycleCount B hB := by
      rw [liftPieces_card, liftPieces_card, hcardA, hcardB]

/-- Any subfamily of an exact pure-cycle partition has even spanning union. -/
theorem even_subfamily {D C : Finset G.Subgraph} (hD : IsPureDecomposition G D)
    (hCD : C ⊆ D) : IsEven (piecesGraph C) :=
  even_piecesGraph (hD.2.1.subset hCD) (fun S hS => hD.1 S (hCD hS))

/-- Hereditary optimality: a subfamily of a minimum partition is itself minimum. -/
theorem minCycleCount_subfamily {D C : Finset G.Subgraph} {hG : IsEven G}
    (hD : IsOptimal hG D) (hCD : C ⊆ D) :
    minCycleCount (piecesGraph C) (even_subfamily hD.1 hCD) = C.card := by
  have hCC := pureDecomposition_piecesOnUnion
    (hD.1.2.1.subset hCD) (fun S hS => hD.1.1 S (hCD hS))
  have hrest : D \ C ⊆ D := Finset.sdiff_subset
  have hRR := pureDecomposition_piecesOnUnion
    (hD.1.2.1.subset hrest) (fun S hS => hD.1.1 S (hrest hS))
  have hCbound := minCycleCount_le_card (even_subfamily hD.1 hCD) hCC
  have hRbound := minCycleCount_le_card (even_subfamily hD.1 hrest) hRR
  rw [piecesOnUnion_card] at hCbound hRbound
  have hcomp := complement_piecesGraph_eq hD.1.2 hCD
  have hdisj : Disjoint (piecesGraph C) (piecesGraph (D \ C)) := by
    rw [← hcomp]
    exact disjoint_sdiff_self_right
  have hcover : piecesGraph C ⊔ piecesGraph (D \ C) = G := by
    rw [← hcomp]
    exact sup_sdiff_cancel_right (piecesGraph_le C)
  have hbound := minCycleCount_le_add hG (even_subfamily hD.1 hCD)
    (even_subfamily hD.1 hrest) (piecesGraph_le C) (piecesGraph_le (D \ C)) hdisj hcover
  have hcard := Finset.card_sdiff_add_card_eq_card hCD
  have hopt := hD.2
  omega

/-- The actual reinterpreted subfamily attains that minimum, with no pieces identified. -/
theorem IsOptimal.subfamily {D C : Finset G.Subgraph} {hG : IsEven G}
    (hD : IsOptimal hG D) (hCD : C ⊆ D) :
    IsOptimal (even_subfamily hD.1 hCD) (piecesOnUnion C) := by
  refine ⟨pureDecomposition_piecesOnUnion (hD.1.2.1.subset hCD)
    (fun S hS => hD.1.1 S (hCD hS)), ?_⟩
  rw [piecesOnUnion_card, minCycleCount_subfamily hD hCD]

/-- Adjoin a specified original pure cycle to any pure partition of its edge complement. -/
theorem pureDecomposition_insert_liftPieces (S : G.Subgraph) (hS : IsPureCycle S)
    {D : Finset (G \ S.spanningCoe).Subgraph}
    (hD : IsPureDecomposition (G \ S.spanningCoe) D) :
    IsPureDecomposition G (insert S (liftPieces (show G \ S.spanningCoe ≤ G from sdiff_le) D)) := by
  refine ⟨?_, isDecomposition_insert_liftPieces S hD.2⟩
  intro T hT
  rcases Finset.mem_insert.mp hT with rfl | hT
  · exact hS
  · exact liftPieces_pureCycle sdiff_le hD.1 T hT

/-- The adjoined cycle is new: nonempty cycle edges cannot lie in their own complement. -/
theorem card_insert_cycle (S : G.Subgraph) (hS : IsPureCycle S)
    (D : Finset (G \ S.spanningCoe).Subgraph) :
    (insert S (liftPieces (show G \ S.spanningCoe ≤ G from sdiff_le) D)).card = D.card + 1 := by
  have hnot : S ∉ liftPieces (show G \ S.spanningCoe ≤ G from sdiff_le) D := by
    intro hmem
    obtain ⟨T, _, heq⟩ := (mem_liftPieces sdiff_le D S).mp hmem
    obtain ⟨v, w, hvw⟩ := hS.exists_adj
    have hT : T.Adj v w := by
      change (liftSubgraph (show G \ S.spanningCoe ≤ G from sdiff_le) T).Adj v w
      rw [heq]
      exact hvw
    exact (T.adj_sub hT).2 hvw
  rw [Finset.card_insert_of_notMem hnot, liftPieces_card]

/-- The minimum can increase by at most one when adjoining a disjoint pure cycle. -/
theorem minCycleCount_le_sdiff_add_one (hG : IsEven G) (S : G.Subgraph) (hS : IsPureCycle S) :
    minCycleCount G hG ≤
      minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) + 1 := by
  obtain ⟨D, hD, hcard⟩ := exists_optimal (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS)
  have hle := minCycleCount_le_card hG (pureDecomposition_insert_liftPieces S hS hD)
  rwa [card_insert_cycle S hS, hcard] at hle

/-- If deleting a cycle lowers the minimum by exactly one, it belongs to an optimum. -/
theorem cycle_mem_optimal_of_count_eq (hG : IsEven G) (S : G.Subgraph) (hS : IsPureCycle S)
    (heq : minCycleCount G hG =
      minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) + 1) :
    ∃ D : Finset G.Subgraph, IsOptimal hG D ∧ S ∈ D := by
  obtain ⟨D, hD, hcard⟩ := exists_optimal (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS)
  refine ⟨insert S (liftPieces (show G \ S.spanningCoe ≤ G from sdiff_le) D),
    ⟨pureDecomposition_insert_liftPieces S hS hD, ?_⟩, Finset.mem_insert_self _ _⟩
  rw [card_insert_cycle S hS, hcard, heq]

/- ## OC and monotone count-bound costs -/

/-- Every original pure-cycle subgraph is a member of some minimum pure partition. -/
def OC (G : SimpleGraph V) (hG : IsEven G) : Prop :=
  ∀ S : G.Subgraph, IsPureCycle S → ∃ D : Finset G.Subgraph, IsOptimal hG D ∧ S ∈ D

/-- Edgeless graphs have OC vacuously, for any number of isolated vertices. -/
theorem oc_bot : OC (⊥ : SimpleGraph V) even_bot := by
  intro S hS
  obtain ⟨v, w, hvw⟩ := hS.exists_adj
  exact (S.adj_sub hvw).elim

/-- In particular OC covers every simple cyclic walk, as an exact original subgraph. -/
theorem OC.walk_mem_optimal {hG : IsEven G} (hOC : OC G hG)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    ∃ D : Finset G.Subgraph, IsOptimal hG D ∧ p.toSubgraph ∈ D :=
  hOC p.toSubgraph (pureCycle_toSubgraph hp)

/-- A real-valued budget on graphs of one fixed finite ambient vertex type. -/
def CountBoundCost (cost : SimpleGraph V → ℝ) (G : SimpleGraph V) (hG : IsEven G) : Prop :=
  (minCycleCount G hG : ℝ) ≤ cost G

/-- The cost statement is exactly existence of a bounded original pure-cycle partition. -/
theorem countBoundCost_iff (cost : SimpleGraph V → ℝ) (hG : IsEven G) :
    CountBoundCost cost G hG ↔
      ∃ D : Finset G.Subgraph, IsPureDecomposition G D ∧ (D.card : ℝ) ≤ cost G := by
  constructor
  · intro hbound
    obtain ⟨D, hD, hcard⟩ := exists_optimal G hG
    exact ⟨D, hD, by simpa only [hcard] using hbound⟩
  · rintro ⟨D, hD, hbound⟩
    exact (show (minCycleCount G hG : ℝ) ≤ (D.card : ℝ) by
      exact_mod_cast minCycleCount_le_card hG hD).trans hbound

/--
In an edge-minimal counterexample to a monotone real budget, deleting ANY pure
cycle lowers the optimum by exactly one. Real costs need not be integral.
-/
theorem count_eq_sdiff_add_one_of_minimal_counterexample
    (cost : SimpleGraph V → ℝ) (hcost : Monotone cost) (hG : IsEven G)
    (hbad : ¬ CountBoundCost cost G hG)
    (hsmall : ∀ H : SimpleGraph V, H < G → ∀ hH : IsEven H, CountBoundCost cost H hH)
    (S : G.Subgraph) (hS : IsPureCycle S) :
    minCycleCount G hG =
      minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) + 1 := by
  have hR := hsmall (G \ S.spanningCoe) (sdiff_pureCycle_lt S hS)
    (even_sdiff_pureCycle hG S hS)
  have hltReal : (minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) : ℝ) <
      (minCycleCount G hG : ℝ) :=
    lt_of_le_of_lt (hR.trans (hcost sdiff_le)) (lt_of_not_ge hbad)
  have hlt : minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) <
      minCycleCount G hG := by exact_mod_cast hltReal
  have hle := minCycleCount_le_sdiff_add_one hG S hS
  omega

/-- Every edge-minimal counterexample to a monotone budget has OC. -/
theorem oc_of_minimal_counterexample
    (cost : SimpleGraph V → ℝ) (hcost : Monotone cost) (hG : IsEven G)
    (hbad : ¬ CountBoundCost cost G hG)
    (hsmall : ∀ H : SimpleGraph V, H < G → ∀ hH : IsEven H, CountBoundCost cost H hH) :
    OC G hG := by
  intro S hS
  exact cycle_mem_optimal_of_count_eq hG S hS
    (count_eq_sdiff_add_one_of_minimal_counterexample cost hcost hG hbad hsmall S hS)

/--
Strong edge-induction sufficiency: a monotone budget valid for all OC even graphs
is valid for every even graph on this SAME vertex type. Empty graphs and all
isolated vertices are included in both the hypothesis and the conclusion.
-/
theorem countBoundCost_of_oc (cost : SimpleGraph V → ℝ) (hcost : Monotone cost)
    (hOC : ∀ G : SimpleGraph V, ∀ hG : IsEven G, OC G hG → CountBoundCost cost G hG) :
    ∀ G : SimpleGraph V, ∀ hG : IsEven G, CountBoundCost cost G hG := by
  intro G
  induction G using WellFoundedLT.induction with
  | ind G ih =>
    intro hG
    by_cases hbound : CountBoundCost cost G hG
    · exact hbound
    · exact hOC G hG (oc_of_minimal_counterexample cost hcost hG hbound ih)

/-- Bounding all graphs with OC is equivalent to bounding all finite even graphs, at fixed order. -/
theorem countBoundCost_iff_oc (cost : SimpleGraph V → ℝ) (hcost : Monotone cost) :
    (∀ G : SimpleGraph V, ∀ hG : IsEven G, CountBoundCost cost G hG) ↔
      ∀ G : SimpleGraph V, ∀ hG : IsEven G, OC G hG → CountBoundCost cost G hG :=
  ⟨fun h G hG _ => h G hG, countBoundCost_of_oc cost hcost⟩

/-- Strict spanning-subgraph inclusion strictly decreases the finite number of edges. -/
theorem card_edges_lt_of_lt (hHG : H < G) : H.edgeFinset.card < G.edgeFinset.card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨edgeFinset_mono hHG.le, fun h => hHG.ne (edgeFinset_inj.mp h)⟩

/--
If a monotone cost fails at this ambient order, there is a counterexample with
minimum edge count among ALL even graphs on this vertex type, and it has OC.
No isolated vertices are discarded in choosing this minimum.
-/
theorem exists_edge_minimal_oc_counterexample
    (cost : SimpleGraph V → ℝ) (hcost : Monotone cost)
    (hfail : ∃ G : SimpleGraph V, ∃ hG : IsEven G, ¬ CountBoundCost cost G hG) :
    ∃ G : SimpleGraph V, ∃ hG : IsEven G,
      ¬ CountBoundCost cost G hG ∧ OC G hG ∧
      ∀ H : SimpleGraph V, ∀ hH : IsEven H, ¬ CountBoundCost cost H hH →
        G.edgeFinset.card ≤ H.edgeFinset.card := by
  let bad : Set (SimpleGraph V) := {G | ∃ hG : IsEven G, ¬ CountBoundCost cost G hG}
  obtain ⟨G, ⟨hG, hbad⟩, hmin⟩ := Set.exists_min_image bad
    (fun H => H.edgeFinset.card) bad.toFinite hfail
  have hsmall : ∀ H : SimpleGraph V, H < G → ∀ hH : IsEven H, CountBoundCost cost H hH := by
    intro H hHG hH
    by_contra hbadH
    have hle := hmin H ⟨hH, hbadH⟩
    have hlt := card_edges_lt_of_lt hHG
    omega
  exact ⟨G, hG, hbad, oc_of_minimal_counterexample cost hcost hG hbad hsmall,
    fun H hH hbadH => hmin H ⟨hH, hbadH⟩⟩

/--
For an integer-valued monotone budget, a minimal counterexample exceeds the
budget by EXACTLY one. Every cycle complement has optimum equal to the old
budget and preserves the budget value. This is the rank-free saturation lemma;
no graphic-rank interpretation or connected-complement conclusion is asserted.
-/
theorem nat_cost_saturation_of_minimal_counterexample
    (cost : SimpleGraph V → ℕ) (hcost : Monotone cost) (hG : IsEven G)
    (hbad : cost G < minCycleCount G hG)
    (hsmall : ∀ H : SimpleGraph V, H < G → ∀ hH : IsEven H, minCycleCount H hH ≤ cost H) :
    minCycleCount G hG = cost G + 1 ∧
      ∀ S : G.Subgraph, ∀ hS : IsPureCycle S,
        minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) = cost G ∧
        cost (G \ S.spanningCoe) = cost G := by
  have hsaturate : ∀ S : G.Subgraph, ∀ hS : IsPureCycle S,
      minCycleCount G hG = cost G + 1 ∧
        minCycleCount (G \ S.spanningCoe) (even_sdiff_pureCycle hG S hS) = cost G ∧
        cost (G \ S.spanningCoe) = cost G := by
    intro S hS
    have hR := hsmall (G \ S.spanningCoe) (sdiff_pureCycle_lt S hS)
      (even_sdiff_pureCycle hG S hS)
    have hmono : cost (G \ S.spanningCoe) ≤ cost G := hcost sdiff_le
    have hglue := minCycleCount_le_sdiff_add_one hG S hS
    omega
  obtain ⟨D, hD, hcard⟩ := exists_optimal G hG
  have hpos : 0 < D.card := by omega
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hpos
  exact ⟨(hsaturate S (hD.1 S hS)).1, fun T hT => (hsaturate T hT).2⟩

/- ## Specialization to a linear budget at the same ambient order -/

/--
Fixed-order sufficiency for a hypothetical OC linear bound. The cost is the
constant `K * |V|` on all graphs on `V`, so it is monotone even when `K < 0`.
-/
theorem pureCycle_bound_of_oc_linear_bound (K : ℝ)
    (hOC : ∀ G : SimpleGraph V, ∀ hG : IsEven G, OC G hG →
      (minCycleCount G hG : ℝ) ≤ K * (Fintype.card V : ℝ))
    (G : SimpleGraph V) (hG : IsEven G) :
    ∃ D : Finset G.Subgraph, IsPureDecomposition G D ∧
      (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) := by
  exact (countBoundCost_iff (fun _ => K * (Fintype.card V : ℝ)) hG).mp
    (countBoundCost_of_oc (fun _ => K * (Fintype.card V : ℝ)) (fun _ _ _ => le_rfl) hOC G hG)

/--
At fixed ambient order, the hypothetical OC bound also gives original
cycle-or-edge partitions of arbitrary graphs, with parity-forest cost `|V| - 1`.
-/
theorem decomposition_bound_of_oc_linear_bound (K : ℝ)
    (hOC : ∀ E : SimpleGraph V, ∀ hE : IsEven E, OC E hE →
      (minCycleCount E hE : ℝ) ≤ K * (Fintype.card V : ℝ)) (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
      (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) + ((Fintype.card V - 1 : ℕ) : ℝ) := by
  apply EvenReduction.decomposition_bound_of_even_bound K _ G
  intro E hE
  obtain ⟨D, hD, hcard⟩ := pureCycle_bound_of_oc_linear_bound K hOC E hE
  exact ⟨D, fun S hS => (hD.1 S hS).isCycleOrEdge, hD.2, hcard⟩

/-- A hypothetical uniform bound ONLY for finite even graphs with OC. -/
def UniformOCLinearBound (K : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V), ∀ hG : IsEven G,
    OC G hG → (minCycleCount G hG : ℝ) ≤ K * (Fintype.card V : ℝ)

/-- For each fixed `K`, the uniform OC and all-even pure-cycle bounds are equivalent. -/
theorem uniform_even_pureCycle_bound_iff_oc (K : ℝ) :
    UniformEvenPureCycleBound.{u} K ↔ UniformOCLinearBound.{u} K := by
  constructor
  · intro h V _ _ G hG _
    obtain ⟨D, hpieces, hD, hcard⟩ := h G hG
    exact (show (minCycleCount G hG : ℝ) ≤ (D.card : ℝ) by
      exact_mod_cast minCycleCount_le_card hG ⟨hpieces, hD⟩).trans hcard
  · intro h V _ _ G hG
    obtain ⟨D, hD, hcard⟩ := pureCycle_bound_of_oc_linear_bound K (h (V := V)) G hG
    exact ⟨D, hD.1, hD.2, hcard⟩

/-- Conditional transfer to the original all-graph cycle-or-edge bound, with constant `K + 1`. -/
theorem uniform_linear_bound_of_oc (K : ℝ) (hOC : UniformOCLinearBound.{u} K) :
    UniformEquivalence.UniformLinearBound.{u} (K + 1) :=
  EvenReduction.uniform_linear_bound_of_even_cycles K
    ((uniform_even_pureCycle_bound_iff_oc K).mpr hOC)

/-- Conditional implication only: no constant satisfying the OC hypothesis is supplied. -/
theorem asymptotic_of_oc_linear_bound (K : ℝ) (hOC : UniformOCLinearBound.{u} K) :
    UniformEquivalence.ExactTarget.{u} :=
  EvenReduction.asymptotic_of_even_cycle_bound K
    ((uniform_even_pureCycle_bound_iff_oc K).mpr hOC)

/-- This is an equivalence of unproved bound propositions, not a proof of either side. -/
theorem asymptotic_iff_exists_oc_linear_bound :
    UniformEquivalence.ExactTarget.{u} ↔ ∃ K : ℝ, 0 ≤ K ∧ UniformOCLinearBound.{u} K := by
  rw [asymptotic_iff_uniform_even_pureCycle_bound]
  exact exists_congr (fun K => and_congr_right
    (fun _ => uniform_even_pureCycle_bound_iff_oc K))

end Erdos184.OptimalCycles
