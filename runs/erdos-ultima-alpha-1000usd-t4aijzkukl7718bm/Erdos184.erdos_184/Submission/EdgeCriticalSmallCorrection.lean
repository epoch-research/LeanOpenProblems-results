import Submission.MinimumParityForest

/-! Parity corrections of at most two edges in edge-critical graphs.
This is an auxiliary exactness result, not a proof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.EdgeCriticalSmallCorrection
open Critical SingletonExchange
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma delete_at_most_one_to_even (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hSG : (S : Set (Sym2 V)) ⊆ G.edgeSet) (hS : S.card ≤ 1)
    (he : ∀ v, Even (Nat.card ((G.deleteEdges (S : Set (Sym2 V))).neighborSet v))) :
    number G = number (G.deleteEdges (S : Set (Sym2 V))) + S.card := by
  by_cases hz : S.card = 0
  · have hzero := Finset.card_eq_zero.mp hz
    subst S
    simp
  · have ho : S.card = 1 := by omega
    obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp ho
    have heG : e ∈ G.edgeSet := hSG (by simp)
    have h := SingleAddition.remove_edge_to_even_number G ⟨e, heG⟩ (by
      simpa only [Finset.coe_singleton, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using he)
    simpa only [Finset.coe_singleton, Finset.card_singleton] using h

lemma delete_at_most_two_to_even (G : SimpleGraph V) (hc : EdgeCritical G)
    (S : Finset (Sym2 V)) (hSG : (S : Set (Sym2 V)) ⊆ G.edgeSet)
    (hS : S.card ≤ 2)
    (he : ∀ v, Even (Nat.card ((G.deleteEdges (S : Set (Sym2 V))).neighborSet v))) :
    number G = number (G.deleteEdges (S : Set (Sym2 V))) + S.card := by
  by_cases hz : S = ∅
  · subst S
    simp
  obtain ⟨e, heS⟩ := Finset.nonempty_iff_ne_empty.mpr hz
  let R := G.deleteEdges {e}
  have hcount : (S.erase e).card + 1 = S.card := Finset.card_erase_add_one heS
  have hsub : (↑(S.erase e) : Set (Sym2 V)) ⊆ R.edgeSet := by
    intro f hf
    rw [SimpleGraph.edgeSet_deleteEdges]
    have h := Finset.mem_erase.mp hf
    exact ⟨hSG h.2, by simpa only [Set.mem_singleton_iff] using h.1⟩
  have hdel : R.deleteEdges (↑(S.erase e) : Set (Sym2 V)) =
      G.deleteEdges (S : Set (Sym2 V)) := by
    dsimp only [R]
    rw [SimpleGraph.deleteEdges_deleteEdges]
    congr 1
    ext f
    simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, hf⟩)
      · exact heS
      · exact hf
    · intro hf
      by_cases hfe : f = e
      · exact Or.inl hfe
      · exact Or.inr ⟨hfe, hf⟩
  have hr := delete_at_most_one_to_even R (S.erase e) hsub (by omega) (by
    rw [hdel]
    exact he)
  rw [hdel] at hr
  have hg := hc ⟨e, hSG heS⟩
  change number G = number R + 1 at hg
  omega

/-- Any parity correction of size at most two is optimal if every edge is
exposable as a singleton in a minimum decomposition. No minimum-cardinality
assumption on the correction is needed. -/
lemma optimal_of_card_le_two {G T : SimpleGraph V} (hc : EdgeCritical G)
    (hTG : T ≤ G) (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v)))
    (hT : Nat.card T.edgeSet ≤ 2) : Optimal G T := by
  have hdel : G.deleteEdges (↑T.edgeFinset : Set (Sym2 V)) = G \ T := by
    ext x y
    simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sdiff_adj,
      Finset.mem_coe, SimpleGraph.mem_edgeFinset]
    rfl
  have h := delete_at_most_two_to_even G hc T.edgeFinset (by
    intro e heT
    exact SimpleGraph.edgeSet_mono hTG (SimpleGraph.mem_edgeFinset.mp heT)) (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hT) (by
        rw [hdel]
        exact he)
  rw [hdel] at h
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h
  exact ⟨hTG, he, h.symm⟩

/-- A smaller-than-Best parity correction in an edge-critical graph must
contain at least three edges. This does not exclude larger corrections. -/
lemma smaller_correction_three_le {G F T : SimpleGraph V} (hc : EdgeCritical G)
    (hb : Best G F) (hTG : T ≤ G)
    (he : ∀ v, Even (Nat.card ((G \ T).neighborSet v)))
    (hlt : Nat.card T.edgeSet < Nat.card F.edgeSet) :
    3 ≤ Nat.card T.edgeSet := by
  by_contra hn
  have ho := optimal_of_card_le_two hc hTG he (by omega)
  have hmin := hb.2 T ho
  omega

end Erdos184Work.EdgeCriticalSmallCorrection
#print axioms Erdos184Work.EdgeCriticalSmallCorrection.optimal_of_card_le_two
#print axioms Erdos184Work.EdgeCriticalSmallCorrection.smaller_correction_three_le
