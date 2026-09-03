import Submission.Spec

/-!
# Auxiliary infrastructure for cycle/edge decompositions

This file uses only the definitions from `Submission.Spec`, not either of its
unproved statements. It constructs the elementary decomposition into individual
edges, defines its minimum possible size, and relates two formulations of a
*conditional* linear bound. None of these results establishes the linear bound
required by Erdős problem 184.
-/

open Filter SimpleGraph
open scoped Classical

namespace Erdos184.DecompositionAux

universe u

variable {V : Type u}

/-- The subgraph supported on the endpoints of one ambient edge. -/
def edgePiece (G : SimpleGraph V) (e : G.edgeSet) : G.Subgraph where
  verts := {v | v ∈ (e : Sym2 V)}
  Adj v w := s(v, w) = (e : Sym2 V)
  adj_sub h := by
    rw [← G.mem_edgeSet, h]
    exact e.property
  edge_vert h := by
    change _ ∈ (e : Sym2 V)
    rw [← h]
    simp
  symm _ _ h := Sym2.eq_swap.trans h

@[simp]
theorem edgePiece_edgeSet (G : SimpleGraph V) (e : G.edgeSet) :
    (edgePiece G e).edgeSet = {(e : Sym2 V)} := by
  ext x
  induction x using Sym2.ind with
  | h v w => rfl

/-- Different ambient edges give different pieces. -/
theorem edgePiece_injective (G : SimpleGraph V) : Function.Injective (edgePiece G) := by
  intro e f h
  apply Subtype.ext
  apply Set.singleton_injective
  simpa only [edgePiece_edgeSet] using congrArg Subgraph.edgeSet h

section Finite

variable [Fintype V]

/-- Passing to the vertex subtype of a subgraph preserves its number of edges. -/
theorem coe_edgeFinset_card (G : SimpleGraph V) (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
    ← H.image_coe_edgeSet_coe]
  exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm

@[simp]
theorem edgePiece_card (G : SimpleGraph V) (e : G.edgeSet) :
    (edgePiece G e).coe.edgeFinset.card = 1 := by
  rw [coe_edgeFinset_card, edgePiece_edgeSet, Set.ncard_singleton]

theorem edgePiece_isCycleOrEdge (G : SimpleGraph V) (e : G.edgeSet) :
    IsCycleOrEdge (edgePiece G e).coe :=
  Or.inr (edgePiece_card G e)

/-- The canonical finite decomposition with one piece for every edge. -/
noncomputable def edgeDecomposition (G : SimpleGraph V) : Finset G.Subgraph :=
  Finset.univ.image (edgePiece G)

@[simp]
theorem mem_edgeDecomposition (G : SimpleGraph V) (H : G.Subgraph) :
    H ∈ edgeDecomposition G ↔ ∃ e : G.edgeSet, edgePiece G e = H := by
  simp [edgeDecomposition]

theorem edgeDecomposition_one_edge (G : SimpleGraph V) :
    ∀ H ∈ edgeDecomposition G, H.coe.edgeFinset.card = 1 := by
  intro H hH
  obtain ⟨e, rfl⟩ := (mem_edgeDecomposition G H).mp hH
  exact edgePiece_card G e

theorem edgeDecomposition_isCycleOrEdge (G : SimpleGraph V) :
    ∀ H ∈ edgeDecomposition G, IsCycleOrEdge H.coe := by
  intro H hH
  exact Or.inr (edgeDecomposition_one_edge G H hH)

/-- The singleton ambient edge sets are pairwise disjoint and cover `G.edgeSet`. -/
theorem edgeDecomposition_isDecomposition (G : SimpleGraph V) :
    IsDecomposition G (edgeDecomposition G) := by
  constructor
  · intro H hH K hK hne
    obtain ⟨e, rfl⟩ := (mem_edgeDecomposition G H).mp hH
    obtain ⟨f, rfl⟩ := (mem_edgeDecomposition G K).mp hK
    change Disjoint (edgePiece G e).edgeSet (edgePiece G f).edgeSet
    rw [edgePiece_edgeSet, edgePiece_edgeSet, Set.disjoint_singleton]
    intro hef
    exact hne (congrArg (edgePiece G) (Subtype.ext hef))
  · ext e
    constructor
    · intro he
      obtain ⟨H, _, heH⟩ := Set.mem_iUnion₂.mp he
      exact H.edgeSet_subset heH
    · intro he
      refine Set.mem_iUnion₂.mpr ⟨edgePiece G ⟨e, he⟩, ?_, ?_⟩
      · exact (mem_edgeDecomposition G _).mpr ⟨⟨e, he⟩, rfl⟩
      · simp

@[simp]
theorem edgeDecomposition_card (G : SimpleGraph V) :
    (edgeDecomposition G).card = G.edgeFinset.card := by
  rw [edgeDecomposition, Finset.card_image_of_injective _ (edgePiece_injective G),
    Finset.card_univ, SimpleGraph.card_edgeSet]

/-- Every finite graph admits a finite decomposition into one-edge pieces,
with exactly as many pieces as ambient edges. -/
theorem exists_one_edge_decomposition (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.edgeFinset.card = 1) ∧
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ D.card = G.edgeFinset.card :=
  ⟨edgeDecomposition G, edgeDecomposition_one_edge G,
    edgeDecomposition_isCycleOrEdge G, edgeDecomposition_isDecomposition G,
    edgeDecomposition_card G⟩

/-- The elementary existence and exact-cardinality bound, in the format of the spec. -/
theorem exists_decomposition_card_eq_edges (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ D.card = G.edgeFinset.card :=
  ⟨edgeDecomposition G, edgeDecomposition_isCycleOrEdge G,
    edgeDecomposition_isDecomposition G, edgeDecomposition_card G⟩

private theorem exists_decomposition_card (G : SimpleGraph V) :
    ∃ n : ℕ, ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = n :=
  ⟨G.edgeFinset.card, exists_decomposition_card_eq_edges G⟩

/-- The least number of cycle/edge pieces in a decomposition of `G`. -/
noncomputable def decompositionNumber (G : SimpleGraph V) : ℕ :=
  Nat.find (exists_decomposition_card G)

/-- The minimum decomposition number is attained. -/
theorem exists_minimum_decomposition (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ D.card = decompositionNumber G :=
  Nat.find_spec (exists_decomposition_card G)

/-- Every admissible decomposition bounds the minimum from above. -/
theorem decompositionNumber_le_card (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hpieces : ∀ H ∈ D, IsCycleOrEdge H.coe) (hD : IsDecomposition G D) :
    decompositionNumber G ≤ D.card :=
  Nat.find_min' (exists_decomposition_card G) ⟨D, hpieces, hD, rfl⟩

theorem decompositionNumber_le_edgeFinset_card (G : SimpleGraph V) :
    decompositionNumber G ≤ G.edgeFinset.card := by
  rw [← edgeDecomposition_card G]
  exact decompositionNumber_le_card G (edgeDecomposition G)
    (edgeDecomposition_isCycleOrEdge G) (edgeDecomposition_isDecomposition G)

/-- On a zero-vertex graph the empty family is already a decomposition. -/
theorem empty_isDecomposition_of_card_eq_zero (G : SimpleGraph V)
    (hV : Fintype.card V = 0) : IsDecomposition G ∅ := by
  letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
  have hG : G = ⊥ := Subsingleton.elim _ _
  simp [IsDecomposition, hG]

end Finite

/-- The original existential Big-O formulation, restated using only the spec's
**definitions**. This is a proposition, not a proof of the conjecture. -/
def AsymptoticDecompositionBound : Prop :=
  ∃ f : ℕ → ℝ,
    (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card W)

/-- A single positive real constant gives a linear bound for every finite graph.
The existence of such a constant is not established in this file. -/
def UniformLinearDecompositionBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ C * (Fintype.card W : ℝ)

/-- A uniform linear bound gives the existential Big-O bound by taking `f n = C * n`. -/
theorem asymptoticDecompositionBound_of_uniformLinearDecompositionBound
    (h : UniformLinearDecompositionBound.{u}) : AsymptoticDecompositionBound.{u} := by
  obtain ⟨C, _, hC⟩ := h
  refine ⟨fun n ↦ C * (n : ℝ), ?_, hC⟩
  exact (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop).const_mul_left C

/-- Conversely, Big-O on `ℕ` supplies a global bound at every positive vertex
count. At vertex count zero we use the empty decomposition instead of bounding `f 0`. -/
theorem uniformLinearDecompositionBound_of_asymptoticDecompositionBound
    (h : AsymptoticDecompositionBound.{u}) : UniformLinearDecompositionBound.{u} := by
  obtain ⟨f, hf, hdecomp⟩ := h
  obtain ⟨C, hC, hbound⟩ := Asymptotics.bound_of_isBigO_nat_atTop hf
  refine ⟨C, hC, ?_⟩
  intro W _ _ G
  by_cases hW : Fintype.card W = 0
  · refine ⟨∅, by simp, empty_isDecomposition_of_card_eq_zero G hW, ?_⟩
    simp [hW]
  · obtain ⟨D, hpieces, hD, hcard⟩ := hdecomp G
    refine ⟨D, hpieces, hD, hcard.trans ?_⟩
    have hb := hbound (x := Fintype.card W) (by exact_mod_cast hW)
    exact (Real.le_norm_self _).trans (by simpa only [Real.norm_natCast] using hb)

/-- This equivalence changes only the formulation of the conjectural bound;
it does not prove either side. -/
theorem asymptoticDecompositionBound_iff_uniformLinearDecompositionBound :
    AsymptoticDecompositionBound.{u} ↔ UniformLinearDecompositionBound.{u} :=
  ⟨uniformLinearDecompositionBound_of_asymptoticDecompositionBound,
    asymptoticDecompositionBound_of_uniformLinearDecompositionBound⟩

/- Dependency audit

Every declaration below is checked independently of the unproved statements in
`Submission.Spec`. Only Lean's standard logical axioms may appear in the output.
-/

#print axioms edgePiece
#print axioms edgePiece_edgeSet
#print axioms edgePiece_injective
#print axioms coe_edgeFinset_card
#print axioms edgePiece_card
#print axioms edgePiece_isCycleOrEdge
#print axioms edgeDecomposition
#print axioms mem_edgeDecomposition
#print axioms edgeDecomposition_one_edge
#print axioms edgeDecomposition_isCycleOrEdge
#print axioms edgeDecomposition_isDecomposition
#print axioms edgeDecomposition_card
#print axioms exists_one_edge_decomposition
#print axioms exists_decomposition_card_eq_edges
#print axioms exists_decomposition_card
#print axioms decompositionNumber
#print axioms exists_minimum_decomposition
#print axioms decompositionNumber_le_card
#print axioms decompositionNumber_le_edgeFinset_card
#print axioms empty_isDecomposition_of_card_eq_zero
#print axioms AsymptoticDecompositionBound
#print axioms UniformLinearDecompositionBound
#print axioms asymptoticDecompositionBound_of_uniformLinearDecompositionBound
#print axioms uniformLinearDecompositionBound_of_asymptoticDecompositionBound
#print axioms asymptoticDecompositionBound_iff_uniformLinearDecompositionBound

end Erdos184.DecompositionAux
