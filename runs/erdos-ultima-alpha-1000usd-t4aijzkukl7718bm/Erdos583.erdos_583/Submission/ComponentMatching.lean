import Submission.Work

/-! Matching addition between distinct components of an all-odd graph. -/
open SimpleGraph Erdos583Work
namespace Erdos583ComponentMatchingDevelopment

lemma avoid_of_unreachable {V : Type*} {H : SimpleGraph V} {u v a b : V}
    (p : H.Walk u v) (ha : a=u ∨ a=v) (hab : ¬H.Reachable a b) :
    b ∉ p.support := by
  classical
  intro hb
  rcases ha with rfl | rfl
  · exact hab (p.takeUntil b hb).reachable
  · exact hab (p.reverse.takeUntil b (by simpa using hb)).reachable

lemma matching_edges_disjoint {V : Type*} {H G : SimpleGraph V}
    (M : MatchingAppend.OrientedMatching G)
    (hsep : ∀ a ∈ M.sources, ¬H.Reachable a (M.target a)) :
    Disjoint H.edgeSet M.edges := by
  apply Set.disjoint_left.mpr
  rintro e he ⟨a, ha, rfl⟩
  exact hsep a ha (SimpleGraph.Adj.reachable he)

/-- Each old path stays in an old connected component, so its endpoints
simultaneously avoid their matched partners. The old graph may have cycles;
no assertion is made for matching edges within one old component. -/
lemma intercomponent_matching_addition {V : Type*} [Fintype V]
    (H G : SimpleGraph V) (ho : ∀ v, Odd (Nat.card (H.neighborSet v)))
    (hHG : H ≤ G) (M : MatchingAppend.OrientedMatching G)
    (hcover : G.edgeSet=H.edgeSet ∪ M.edges)
    (hsep : ∀ a ∈ M.sources, ¬H.Reachable a (M.target a)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card ≤ Fintype.card V := by
  classical
  obtain ⟨k, _, ⟨T⟩⟩ := all_odd_normal_trail_system H (by
    simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using ho)
  obtain ⟨S, hS⟩ := T.exists_max_score
  apply MatchingAppend.matching_append_certificate hHG M S
    (TrailNormalization.max_score_isPath S hS) (matching_edges_disjoint M hsep) hcover
  intro i a ha hs
  exact avoid_of_unreachable (S.walk i) ha (hsep a hs)

lemma gallai_of_intercomponent_matching {V : Type*} [Fintype V]
    (H G : SimpleGraph V) (ho : ∀ v, Odd (Nat.card (H.neighborSet v)))
    (hHG : H ≤ G) (M : MatchingAppend.OrientedMatching G)
    (hcover : G.edgeSet=H.edgeSet ∪ M.edges)
    (hsep : ∀ a ∈ M.sources, ¬H.Reachable a (M.target a)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨D, hD, hcard⟩ := intercomponent_matching_addition H G ho hHG M hcover hsep
  refine ⟨D, hD, ?_⟩
  have hc := Nat.le_ceil ((Fintype.card V : ℚ)/2)
  exact_mod_cast (show (D.card : ℚ) ≤ (⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) by
    have hn : 2*(D.card : ℚ) ≤ Fintype.card V := by exact_mod_cast hcard
    linarith)

end Erdos583ComponentMatchingDevelopment
