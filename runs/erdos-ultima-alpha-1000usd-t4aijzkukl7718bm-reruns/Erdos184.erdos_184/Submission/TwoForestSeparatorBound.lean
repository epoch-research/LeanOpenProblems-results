import Submission.ForestBoundaryBudget
import Submission.ExactVertexSmoothing

/-! An even union of two forests has at most |S|-1 cycles in any pure
partition, when the forests' support intersection lies in S. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.ForestBoundaryBudget
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

lemma even_left_outside_separator {G A B : SimpleGraph V} (S : Set V)
    (heG : ∀ x, Even (G.degree x))
    (_hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S) : ∀ x, x ∉ S → Even (A.degree x) := by
  intro x hx
  by_cases hxA : x ∈ A.support
  · have hxB : x ∉ B.support := fun h => hx (hi ⟨hxA,h⟩)
    have hh := degree_eq_of_other_unsupported hu x hxB
    have he := heG x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh he ⊢
    rwa [hh]
  · rw [(A.degree_eq_zero_iff_notMem_support x).mpr hxA]
    decide

lemma two_forest_decomposition_bound {G A B : SimpleGraph V} (S : Set V)
    (heG : ∀ x, Even (G.degree x)) (hA : A.IsAcyclic) (hB : B.IsAcyclic)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S)
    (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    D.card ≤ S.ncard-1 := by
  let X := fun H : G.Subgraph => H.spanningCoe ⊓ A
  let Y := fun H : G.Subgraph => H.spanningCoe ⊓ B
  have hXe (H : G.Subgraph) : (X H).edgeSet = H.edgeSet ∩ A.edgeSet := by
    dsimp only [X]; rw [edgeSet_inf]; rfl
  have hYe (H : G.Subgraph) : (Y H).edgeSet = H.edgeSet ∩ B.edgeSet := by
    dsimp only [Y]; rw [edgeSet_inf]; rfl
  have hX (H : G.Subgraph) : X H ≤ A := inf_le_right
  have hY (H : G.Subgraph) : Y H ≤ B := inf_le_right
  have heA := even_left_outside_separator S heG hd hu hi
  apply forest_family_card_bound D X A hA S heA (fun H _ => hX H)
  · intro H hH hbot
    obtain ⟨e,heH,henB⟩ := cycle_has_edge_outside_forest B hB H (hcD H hH).1 (hcD H hH).2
    have heG : e ∈ G.edgeSet := H.edgeSet_subset heH
    rw [← hu] at heG
    have heA := heG.resolve_right henB
    have heX : e ∈ (X H).edgeSet := by rw [hXe]; exact ⟨heH,heA⟩
    simp only [hbot,edgeSet_bot,Set.mem_empty_iff_false] at heX
  · intro H hH
    have heH : ∀ x, Even (H.spanningCoe.degree x) := by
      intro x
      rw [Subgraph.degree_spanningCoe]
      exact regular_two_piece_degree_even H (hcD H hH).2 x
    have hdXY : Disjoint (X H).edgeSet (Y H).edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he hf
      rw [hXe] at he
      rw [hYe] at hf
      exact Set.disjoint_left.mp hd he.2 hf.2
    have huXY : (X H).edgeSet ∪ (Y H).edgeSet = H.spanningCoe.edgeSet := by
      rw [hXe,hYe]
      ext e
      constructor
      · rintro (h | h) <;> exact h.1
      · intro he
        have heG : e ∈ G.edgeSet := H.edgeSet_subset he
        rw [← hu] at heG
        exact heG.elim (fun h => Or.inl ⟨he,h⟩) (fun h => Or.inr ⟨he,h⟩)
    exact even_left_outside_separator S (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heH x)
      hdXY huXY (fun _ hx => hi ⟨support_mono (hX H) hx.1,support_mono (hY H) hx.2⟩)
  · intro H hH K hK hHK
    apply Set.disjoint_left.mpr
    intro e he hf
    dsimp only at he hf
    rw [hXe] at he hf
    exact Set.disjoint_left.mp (hdD hH hK hHK) he.1 hf.1

lemma two_forest_piece_bound {G A B : SimpleGraph V} (S : Set V)
    (heG : ∀ x, Even (G.degree x)) (hA : A.IsAcyclic) (hB : B.IsAcyclic)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S) : ExactVertexSmoothing.HasPieceBound (S.ncard-1) G := by
  obtain ⟨D,hcD,hdD⟩ := even_cycle_decomposition G heG
  exact ⟨D,hcD,hdD,two_forest_decomposition_bound S heG hA hB hd hu hi D hcD hdD.1⟩

end Erdos184.ForestBoundaryBudget
