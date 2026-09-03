import Submission.Projection

/-! Passing a uniform cycle bound from connected even graphs to all even graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

universe u
lemma even_bound_of_connected_bound (C : ℝ)
    (hbound : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ C * Fintype.card V := by
  intro V _ G heven
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hex : ∀ c : G.ConnectedComponent, ∃ F : Finset G.Subgraph,
      (∀ A ∈ F, A.coe.Connected ∧ A.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (F : Set G.Subgraph) (fun A => A.edgeSet) ∧
      (⋃ A ∈ F, A.edgeSet) = c.toSubgraph.edgeSet ∧
      (F.card : ℝ) ≤ C * Fintype.card c := by
    intro c
    have hc : c.toSubgraph.coe.Connected := by
      rw [c.coe_toSubgraph]
      exact c.connected_toSimpleGraph
    have he : ∀ v, Even (c.toSubgraph.coe.degree v) := by
      have hh : ∀ v : c, Even (c.toSimpleGraph.degree v) := by
        intro v
        rw [component_degree]
        exact heven v.val
      simpa only [c.coe_toSubgraph, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hh
    obtain ⟨E, hcy, hd, hcard⟩ := hbound c.toSubgraph.coe hc (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using he)
    obtain ⟨F, hcF, hdF, heF, hbF⟩ := lift_cycle_decomposition c.toSubgraph E (by
      intro A hA
      refine ⟨(hcy A hA).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcy A hA).2 v) hd
    refine ⟨F, ?_, hdF, heF, ?_⟩
    · intro A hA
      refine ⟨(hcF A hA).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF A hA).2 v
    · have hh : (F.card : ℝ) ≤ E.card := by exact_mod_cast hbF
      have hcard' : (E.card : ℝ) ≤ C * Fintype.card c := by
        simpa only [← Nat.card_eq_fintype_card] using hcard
      exact hh.trans hcard'
  choose F hcF hdF heF hbF using hex
  let D := Finset.univ.biUnion F
  have hsub (c : G.ConnectedComponent) (A : G.Subgraph) (hA : A ∈ F c) :
      A.edgeSet ⊆ c.toSubgraph.edgeSet := by
    intro e he
    rw [← heF c]
    exact Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨hA, he⟩⟩
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨c, _, hA⟩ := Finset.mem_biUnion.mp hA
    refine ⟨(hcF c A hA).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF c A hA).2 v
  · intro A hA A' hA' hAA'
    obtain ⟨c, _, hA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨c', _, hA'⟩ := Finset.mem_biUnion.mp hA'
    by_cases hcc : c = c'
    · subst c'
      exact hdF c hA hA' hAA'
    · apply Set.disjoint_left.mpr
      intro e he he'
      have h1 := hsub c A hA he
      have h2 := hsub c' A' hA' he'
      induction e using Sym2.ind with
      | h x y =>
        exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hcc)
          (c.toSubgraph.edge_vert h1) (c'.toSubgraph.edge_vert h2)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨A, _, he⟩
      exact A.edgeSet_subset he
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        let c := G.connectedComponentMk x
        have hec : s(x, y) ∈ c.toSubgraph.edgeSet := by
          exact ⟨ConnectedComponent.connectedComponentMk_mem,
            c.mem_supp_of_adj_mem_supp ConnectedComponent.connectedComponentMk_mem he, he⟩
        rw [← heF c] at hec
        simp only [Set.mem_iUnion] at hec
        obtain ⟨A, hA, heA⟩ := hec
        exact ⟨A, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hA⟩, heA⟩
  · have hsum : ∑ c : G.ConnectedComponent, Fintype.card c = Fintype.card V := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
    have hsum' : (∑ c : G.ConnectedComponent, (Fintype.card c : ℝ)) = Fintype.card V := by
      exact_mod_cast hsum
    calc
      (D.card : ℝ) ≤ ∑ c, ((F c).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := F))
      _ ≤ ∑ c : G.ConnectedComponent, C * Fintype.card c := Finset.sum_le_sum (fun c _ => hbF c)
      _ = C * Fintype.card V := by rw [← Finset.mul_sum, hsum']

end Erdos184
