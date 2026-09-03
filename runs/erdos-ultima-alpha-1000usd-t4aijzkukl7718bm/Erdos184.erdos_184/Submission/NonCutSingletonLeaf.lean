import Submission.OptimalSingletonForest

/-! A forest in a connected graph has a vertex of forest degree at most one
whose deletion leaves the ambient graph connected. This selection statement
alone does not bound the loss of the cycle-and-edge decomposition number. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.NonCutSingletonLeaf
open SingletonExchange

variable {V : Type*} [Fintype V] [Nontrivial V]

lemma exists_noncut_low_forest_degree {G F : SimpleGraph V}
    (hG : G.Connected) (hFG : F ≤ G) (hF : F.IsAcyclic) :
    ∃ v : V, (G.induce ({v}ᶜ : Set V)).Connected ∧
      Nat.card (F.neighborSet v) ≤ 1 := by
  obtain ⟨T, hFT, hTm⟩ :=
    SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic hFG hF
  have hTG : T ≤ G := hTm.1.1
  have ht : T.IsTree := (hG.maximal_le_isAcyclic_iff_isTree hTG).mp hTm
  obtain ⟨v, hv⟩ := ht.exists_vert_degree_one_of_nontrivial
  refine ⟨v, (ht.isConnected.induce_compl_singleton_of_degree_eq_one hv).mono ?_, ?_⟩
  · intro x y hxy
    exact hTG hxy
  · have hd : F.degree v ≤ T.degree v := SimpleGraph.degree_le_of_le hFT
    rw [hv] at hd
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hd

lemma exists_noncut_low_optimal_degree {G F : SimpleGraph V}
    (hG : G.Connected) (hF : Optimal G F) :
    ∃ v : V, (G.induce ({v}ᶜ : Set V)).Connected ∧
      Nat.card (F.neighborSet v) ≤ 1 :=
  exists_noncut_low_forest_degree hG hF.1 hF.acyclic

lemma exists_noncut_low_best_degree {G F : SimpleGraph V}
    (hG : G.Connected) (hF : Best G F) :
    ∃ v : V, (G.induce ({v}ᶜ : Set V)).Connected ∧
      Nat.card (F.neighborSet v) ≤ 1 :=
  exists_noncut_low_optimal_degree hG hF.1

end Erdos184Work.NonCutSingletonLeaf

#print axioms Erdos184Work.NonCutSingletonLeaf.exists_noncut_low_forest_degree
#print axioms Erdos184Work.NonCutSingletonLeaf.exists_noncut_low_best_degree
