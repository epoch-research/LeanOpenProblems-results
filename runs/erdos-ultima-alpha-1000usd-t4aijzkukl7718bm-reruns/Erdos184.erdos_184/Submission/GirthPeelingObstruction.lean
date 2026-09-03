import Submission.Cuts
import Submission.Projection

/-! Removing girth-length pieces need not make progress, even in K₅.
This is an obstruction to a proposed iteration, not to Erdős 184. -/
open SimpleGraph
namespace Erdos184.GirthPeelingObstruction

abbrev G : SimpleGraph (Fin 5) := ⊤

def p₀ : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 0) .nil

def p₁ : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) .nil

def triangle : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 0) .nil

lemma p₀_cycle : p₀.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [p₀], by decide⟩

lemma p₁_cycle : p₁.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [p₁], by decide⟩

lemma triangle_cycle : triangle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [triangle], by decide⟩

lemma graph_girth : G.girth = 3 := by
  have hlow := G.three_le_girth (fun ha => ha triangle triangle_cycle)
  have hupp := G.girth_le_length triangle_cycle
  have ht : triangle.length = 3 := rfl
  omega

lemma pieces_ne : p₀.toSubgraph ≠ p₁.toSubgraph := by
  intro h
  have hh := congrArg (fun H : G.Subgraph => s(0,1) ∈ H.edgeSet) h
  simp only [Walk.edgeSet_toSubgraph, Set.mem_setOf_eq] at hh
  have h₀ : s(0,1) ∈ p₀.edges := by decide
  have h₁ : s(0,1) ∉ p₁.edges := by decide
  exact h₁ (hh ▸ h₀)

open scoped Classical
noncomputable def D : Finset G.Subgraph := {p₀.toSubgraph, p₁.toSubgraph}

lemma D_card : D.card = 2 := by simp [D, pieces_ne]

lemma D_cycles : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  simp only [D, Finset.mem_insert, Finset.mem_singleton] at hH
  rcases hH with rfl | rfl
  · have hh := cycle_subgraph_regular G p₀_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v
  · have hh := cycle_subgraph_regular G p₁_cycle
    refine ⟨hh.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v

lemma pieces_disjoint : Disjoint p₀.toSubgraph.edgeSet p₁.toSubgraph.edgeSet := by
  simp only [Walk.edgeSet_toSubgraph, Set.disjoint_left, Set.mem_setOf_eq]
  exact List.disjoint_of_nodup_append (by decide : (p₀.edges ++ p₁.edges).Nodup)

lemma D_decomposition : IsDecomposition G D := by
  constructor
  · intro H hH K hK hne
    simp only [D, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH hK
    rcases hH with rfl | rfl <;> rcases hK with rfl | rfl
    · exact (hne rfl).elim
    · exact pieces_disjoint
    · exact pieces_disjoint.symm
    · exact (hne rfl).elim
  · simp only [D, Finset.mem_insert, Finset.mem_singleton, Set.iUnion_iUnion_eq_or_left,
      Set.iUnion_iUnion_eq_left]
    ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_union, Walk.edgeSet_toSubgraph, Set.mem_setOf_eq]
      change (s(u,v) ∈ p₀.edges ∨ s(u,v) ∈ p₁.edges) ↔ u ≠ v
      fin_cases u <;> fin_cases v <;> decide

lemma graph_regular : G.IsRegularOfDegree 4 := by
  intro v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  change Nat.card {x : Fin 5 // v ≠ x} = 4
  simp

lemma two_le_decomposition_card (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G E) : 2 ≤ E.card := by
  have hh := cycle_decomposition_degree_lower G E (by
    intro H hH
    refine ⟨(hc H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2 v) hd 0
  have hv := graph_regular 0
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hh
  omega

lemma minimum_decomposition_piece_length (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G E)
    (hm : ∀ F : Finset G.Subgraph,
      (∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G F → E.card ≤ F.card) :
    E.card = 2 ∧ ∀ H ∈ E, H.edgeSet.ncard = 5 := by
  have hlow := two_le_decomposition_card E hc hd
  have hupp := hm D D_cycles D_decomposition
  rw [D_card] at hupp
  have hcard : E.card = 2 := by omega
  refine ⟨hcard, ?_⟩
  have hdeg : ∀ v, G.degree v = 2 * E.card := by
    intro v
    have hh := graph_regular v
    simpa only [hcard, ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh
  have hspan := cycle_decomposition_saturated_verts G E (by
    intro H hH
    refine ⟨(hc H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2 v) hd (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hdeg)
  intro H hH
  have hecard := regular_two_edge_vertex_card H (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2 v)
  rw [hecard, hspan H hH]
  simp

/-- A minimum decomposition can have no piece as short as the girth. -/
lemma minimum_decomposition_no_girth_pieces (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G E)
    (hm : ∀ F : Finset G.Subgraph,
      (∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G F → E.card ≤ F.card) :
    E.filter (fun H => H.edgeSet.ncard = G.girth) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro H hH
  rw [(minimum_decomposition_piece_length E hc hd hm).2 H hH, graph_girth]
  decide

def residual : SimpleGraph (Fin 5) := G \ triangle.toSubgraph.spanningCoe

lemma graph_support : G.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  by_cases h : v = 0
  · subst v
    exact ⟨1, by decide⟩
  · exact ⟨0, h⟩

lemma residual_support : residual.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  fin_cases v
  · exact ⟨3, by
      change G.Adj _ _ ∧ ¬triangle.toSubgraph.Adj _ _
      simp [triangle]⟩
  · exact ⟨3, by
      change G.Adj _ _ ∧ ¬triangle.toSubgraph.Adj _ _
      simp [triangle]⟩
  · exact ⟨3, by
      change G.Adj _ _ ∧ ¬triangle.toSubgraph.Adj _ _
      simp [triangle]⟩
  · exact ⟨4, by
      change G.Adj _ _ ∧ ¬triangle.toSubgraph.Adj _ _
      simp [triangle]⟩
  · exact ⟨3, by
      change G.Adj _ _ ∧ ¬triangle.toSubgraph.Adj _ _
      simp [triangle]⟩

lemma triangle_edge_card : triangle.toSubgraph.edgeSet.ncard = 3 := by
  have hh := cycle_subgraph_regular G triangle_cycle
  have he := regular_two_edge_vertex_card triangle.toSubgraph (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh.2 v)
  have hv : triangle.toSubgraph.verts = ({0,1,2} : Set (Fin 5)) := by
    ext v
    rw [Walk.mem_verts_toSubgraph]
    fin_cases v <;> decide
  rw [he, hv]
  simp

lemma prescribed_triangle_three_le (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G E) (hT : triangle.toSubgraph ∈ E) : 3 ≤ E.card := by
  by_contra! hn
  have hm : ∀ F : Finset G.Subgraph,
      (∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G F → E.card ≤ F.card := by
    intro F hcF hdF
    have hb := two_le_decomposition_card F hcF hdF
    omega
  have hh := (minimum_decomposition_piece_length E hc hd hm).2 triangle.toSubgraph hT
  rw [triangle_edge_card] at hh
  omega

/-- Forcing the triangle costs an extra piece, although its deletion makes
no vertex isolated. This refutes a bound on this extra cost using only the
immediate decrease in the number of nonisolated vertices. -/
lemma prescribed_triangle_cost_without_support_loss :
    residual.support = G.support ∧
    D.card = 2 ∧
    (∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → triangle.toSubgraph ∈ E → 3 ≤ E.card) := by
  exact ⟨residual_support.trans graph_support.symm, D_card, prescribed_triangle_three_le⟩

end Erdos184.GirthPeelingObstruction
