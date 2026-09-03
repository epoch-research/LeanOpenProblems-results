import Submission.ChainRingParity

/-! Classifying decomposition pieces relative to the closing edge of the chain. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ChainRing
open Critical MaximumCycles
set_option maxHeartbeats 800000

lemma cycle_piece_even_max (H : source.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∀ v, Even (deg H.spanningCoe v)) ∧ (∀ v, deg H.spanningCoe v ≤ 2) := by
  have hd (v : Vertex) : deg H.spanningCoe v = if v ∈ H.verts then 2 else 0 := by
    have hh := regular_two_spanning_degree H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hH.2) v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh
  constructor
  · intro v
    rw [hd]
    split_ifs <;> decide
  · intro v
    rw [hd]
    split_ifs <;> omega

lemma single_piece_edges (H : source.Subgraph) (hH : H.coe.edgeFinset.card = 1) :
    ∃ e, H.edgeSet = {e} := by
  apply Set.ncard_eq_one.mp
  have hh := (subgraph_edge_card H).trans hH
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hh

lemma piece_edges_nonempty (H : source.Subgraph) (hH : IsCycleOrEdge H.coe) : H.edgeSet.Nonempty := by
  rcases hH with hc | hs
  · exact cycle_piece_edgeSet_nonempty H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc)
  · obtain ⟨e,he⟩ := single_piece_edges H hs
    exact ⟨e,he.symm ▸ Set.mem_singleton e⟩

lemma cycle_without_closing_local (H : source.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (he : ¬ H.spanningCoe.Adj (.inl 0) (.inl 3)) : ∃ i, H.spanningCoe ≤ block i := by
  obtain ⟨e,heH⟩ := cycle_piece_edgeSet_nonempty H (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH)
  have hcode := GraphCircuitCode.cycle_circuit H (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH)
  have heven := (cycle_piece_even_max H hH).1
  induction e using Sym2.ind with | h x y =>
  rcases source_edge_cases x y (H.edgeSet_subset heH) with hc | ⟨i,hi⟩
  · rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (he heH).elim
    · exact (he (show H.spanningCoe.Adj (.inl 0) (.inl 3) from heH.symm)).elim
  · let T := H.spanningCoe ⊓ block i
    have hTe : ∀ v, Even (T.degree v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
        block_even_of_no_closing H.spanningCoe_le heven he i
    have hv : (GraphCircuitCode.code source).valid T.edgeFinset := by
      refine ⟨T,inf_le_left.trans H.spanningCoe_le,?_,?_⟩
      · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hTe
      · ext e
        simp only [SimpleGraph.mem_edgeFinset]
    have hsub : T.edgeFinset ⊆ H.spanningCoe.edgeFinset := SimpleGraph.edgeFinset_mono inf_le_left
    have hn : T.edgeFinset.Nonempty := ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr ⟨heH,hi⟩⟩
    have heq := hcode.2.2 _ hsub hv hn
    have hTG : T = H.spanningCoe := SimpleGraph.edgeFinset_inj.mp heq
    exact ⟨i,hTG ▸ (show T ≤ block i from inf_le_right)⟩

lemma piece_without_closing_local (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : ¬ H.spanningCoe.Adj (.inl 0) (.inl 3)) : ∃ i, H.spanningCoe ≤ block i := by
  rcases hH with hc | hs
  · exact cycle_without_closing_local H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc) he
  · obtain ⟨e,hed⟩ := single_piece_edges H hs
    have heH : e ∈ H.edgeSet := hed.symm ▸ Set.mem_singleton e
    induction e using Sym2.ind with | h x y =>
    rcases source_edge_cases x y (H.edgeSet_subset heH) with hc | ⟨i,hi⟩
    · rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (he heH).elim
      · exact (he (show H.spanningCoe.Adj (.inl 0) (.inl 3) from heH.symm)).elim
    · refine ⟨i,?_⟩
      intro a b hab
      have hm : s(a,b) ∈ H.edgeSet := hab
      rw [hed,Set.mem_singleton_iff] at hm
      change s(a,b) ∈ (block i).edgeSet
      exact hm.symm ▸ hi

lemma single_closing_le (H : source.Subgraph) (hs : H.coe.edgeFinset.card = 1)
    (he : H.spanningCoe.Adj (.inl 0) (.inl 3)) : H.spanningCoe ≤ closing := by
  obtain ⟨e,hed⟩ := single_piece_edges H hs
  have he' : s(Sum.inl 0,Sum.inl 3) = e := by
    have hm : s(Sum.inl 0,Sum.inl 3) ∈ H.edgeSet := he
    simpa only [hed,Set.mem_singleton_iff] using hm
  intro x y hxy
  have hm : s(x,y) ∈ H.edgeSet := hxy
  rw [hed,Set.mem_singleton_iff,← he'] at hm
  change s(x,y) ∈ closing.edgeSet
  rw [hm]
  exact (closing_adj_iff _ _).mpr (Or.inl ⟨rfl,rfl⟩)

lemma closing_piece_block_bound (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : H.spanningCoe.Adj (.inl 0) (.inl 3)) (i : Fin 3) :
    (H.spanningCoe ⊓ block i).edgeFinset.card ≤ 4 := by
  rcases hH with hc | hs
  · have hc' : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    have hh := cycle_piece_even_max H hc'
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using
      closing_block_edge_card_le_four H.spanningCoe_le hh.1 hh.2 he i
  · have hle := single_closing_le H hs he
    have hz : H.spanningCoe ⊓ block i = ⊥ := by
      ext x y
      constructor
      · rintro ⟨hxy,hb⟩
        exact (block_no_closing i x y ⟨hb,hle hxy⟩).elim
      · exact False.elim
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card]
    rw [hz]
    simp

lemma closing_piece_right_even (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : H.spanningCoe.Adj (.inl 0) (.inl 3)) (i : Fin 3) (j : Fin 6) :
    Even (deg H.spanningCoe (.inr (i,j))) := by
  rcases hH with hc | hs
  · exact (cycle_piece_even_max H (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc)).1 _
  · have hle := single_closing_le H hs he
    have hd : deg H.spanningCoe (.inr (i,j)) = 0 := by
      apply degree_zero_of_no_adj
      intro w hw
      have hcw := (closing_adj_iff _ _).mp (hle hw)
      rcases hcw with ⟨h,_⟩ | ⟨h,_⟩ <;> cases h
    rw [hd]
    exact ⟨0,rfl⟩

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.piece_without_closing_local
#print axioms Erdos184Work.ChainRing.closing_piece_block_bound
