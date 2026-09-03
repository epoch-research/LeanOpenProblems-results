import Submission.Spec

/-!
# Infrastructure for Erdős Problem 184

This file uses the definitions in `Submission.Spec`, but neither of its admitted
statements.  The singleton-edge decomposition gives a quadratic bound, not the
linear bound requested by the Erdős–Gallai conjecture.
-/

open Filter SimpleGraph

namespace Erdos184.Infrastructure

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The subgraph consisting of the two endpoints and the single unordered edge `e`. -/
def singleEdgeSubgraph (G : SimpleGraph V) (e : G.edgeSet) : G.Subgraph where
  verts := {v | v ∈ (e : Sym2 V)}
  Adj a b := s(a, b) = (e : Sym2 V)
  adj_sub := by
    intro a b h
    change s(a, b) ∈ G.edgeSet
    rw [h]
    exact e.property
  edge_vert := by
    intro a b h
    change a ∈ (e : Sym2 V)
    rw [← h]
    exact Sym2.mem_mk_left a b
  symm := by
    intro a b h
    exact Sym2.eq_swap.trans h

@[simp]
theorem singleEdgeSubgraph_edgeSet (e : G.edgeSet) :
    (singleEdgeSubgraph G e).edgeSet = {(e : Sym2 V)} := by
  ext x
  induction x using Sym2.ind with
  | h a b => rfl

/-- Distinct unordered edges give distinct single-edge subgraphs. -/
theorem singleEdgeSubgraph_injective (G : SimpleGraph V) :
    Function.Injective (singleEdgeSubgraph G) := by
  intro e f h
  apply Subtype.ext
  have he := congrArg SimpleGraph.Subgraph.edgeSet h
  simpa only [singleEdgeSubgraph_edgeSet, Set.singleton_eq_singleton_iff] using he

section Finite

variable [Fintype V]

open scoped Classical in
/-- Passing from a subgraph to its graph on the subtype of vertices preserves edge count. -/
theorem coe_edgeFinset_card (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  classical
  rw [← H.image_coe_edgeSet_coe,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  exact (Set.ncard_eq_toFinset_card' H.coe.edgeSet).symm

open scoped Classical in
@[simp]
theorem singleEdgeSubgraph_coe_edgeFinset_card (e : G.edgeSet) :
    (singleEdgeSubgraph G e).coe.edgeFinset.card = 1 := by
  rw [coe_edgeFinset_card, singleEdgeSubgraph_edgeSet, Set.ncard_singleton]

open scoped Classical in
/-- A single-edge subgraph satisfies the exact predicate from the problem statement. -/
theorem singleEdgeSubgraph_isCycleOrEdge (e : G.edgeSet) :
    IsCycleOrEdge (singleEdgeSubgraph G e).coe := by
  exact Or.inr (singleEdgeSubgraph_coe_edgeFinset_card e)

/-- The finite family containing one single-edge subgraph for each edge of `G`. -/
noncomputable def singletonEdgeDecomposition (G : SimpleGraph V) : Finset G.Subgraph := by
  classical
  exact Finset.univ.image (singleEdgeSubgraph G)

open scoped Classical in
@[simp]
theorem mem_singletonEdgeDecomposition (H : G.Subgraph) :
    H ∈ singletonEdgeDecomposition G ↔ ∃ e : G.edgeSet, singleEdgeSubgraph G e = H := by
  simp [singletonEdgeDecomposition]

open scoped Classical in
/-- Every piece in the canonical decomposition has exactly one edge. -/
theorem singletonEdgeDecomposition_single_edge :
    ∀ H ∈ singletonEdgeDecomposition G, H.coe.edgeFinset.card = 1 := by
  intro H hH
  obtain ⟨e, rfl⟩ := (mem_singletonEdgeDecomposition H).mp hH
  exact singleEdgeSubgraph_coe_edgeFinset_card e

open scoped Classical in
/-- Every piece in the canonical decomposition is a cycle or an edge. -/
theorem singletonEdgeDecomposition_isCycleOrEdge :
    ∀ H ∈ singletonEdgeDecomposition G, IsCycleOrEdge H.coe := by
  intro H hH
  exact Or.inr (singletonEdgeDecomposition_single_edge H hH)

/-- Single-edge pieces partition the edge set, in the exact sense of `IsDecomposition`. -/
theorem singletonEdgeDecomposition_isDecomposition :
    IsDecomposition G (singletonEdgeDecomposition G) := by
  classical
  constructor
  · intro H hH J hJ hne
    obtain ⟨e, rfl⟩ := (mem_singletonEdgeDecomposition H).mp hH
    obtain ⟨f, rfl⟩ := (mem_singletonEdgeDecomposition J).mp hJ
    change Disjoint (singleEdgeSubgraph G e).edgeSet (singleEdgeSubgraph G f).edgeSet
    rw [singleEdgeSubgraph_edgeSet, singleEdgeSubgraph_edgeSet, Set.disjoint_singleton]
    intro hef
    exact hne (congrArg (singleEdgeSubgraph G) (Subtype.ext hef))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, hH, he⟩
      exact H.edgeSet_subset he
    · intro he
      refine ⟨singleEdgeSubgraph G ⟨e, he⟩, ?_, ?_⟩
      · exact (mem_singletonEdgeDecomposition _).mpr ⟨⟨e, he⟩, rfl⟩
      · simp

open scoped Classical in
/-- The singleton-edge decomposition has exactly as many pieces as `G` has edges. -/
@[simp]
theorem singletonEdgeDecomposition_card :
    (singletonEdgeDecomposition G).card = G.edgeFinset.card := by
  classical
  rw [singletonEdgeDecomposition, Finset.card_image_of_injective _
    (singleEdgeSubgraph_injective G), Finset.card_univ, SimpleGraph.card_edgeSet]

/-- In particular the canonical decomposition has at most `n.choose 2` pieces. -/
theorem singletonEdgeDecomposition_card_le :
    (singletonEdgeDecomposition G).card ≤ (Fintype.card V).choose 2 := by
  classical
  rw [singletonEdgeDecomposition_card]
  exact SimpleGraph.card_edgeFinset_le_card_choose_two

open scoped Classical in
/-- An unconditional decomposition satisfying both the exact edge count and the quadratic bound. -/
theorem exists_singleton_edge_decomposition (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.edgeFinset.card = 1) ∧
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧
      D.card = G.edgeFinset.card ∧
      D.card ≤ (Fintype.card V).choose 2 := by
  exact ⟨singletonEdgeDecomposition G, singletonEdgeDecomposition_single_edge,
    singletonEdgeDecomposition_isCycleOrEdge, singletonEdgeDecomposition_isDecomposition,
    singletonEdgeDecomposition_card, singletonEdgeDecomposition_card_le⟩

open scoped Classical in
/-- A cyclic walk gives a connected, 2-regular graph on its own vertices, hence an admissible piece. -/
theorem isCycleOrEdge_toSubgraph_of_isCycle {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    IsCycleOrEdge p.toSubgraph.coe := by
  classical
  refine Or.inl ⟨p.toSubgraph_connected.coe, ?_⟩
  intro w
  rw [Subgraph.coe_degree, Subgraph.degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp w.property)

end Finite

open scoped Classical in
/--
A uniform real constant giving every graph some decomposition with at most
`K * n` pieces suffices for the exact asymptotic assertion in `Submission.Spec`.
The hypothesis is not proved here; the witness is explicitly `f n = K * n`.
-/
theorem asymptotic_of_uniform_linear_bound (K : ℝ)
    (hK : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  refine ⟨fun n ↦ K * (n : ℝ), Asymptotics.isBigO_const_mul_self K _ _, ?_⟩
  exact hK

end Erdos184.Infrastructure
