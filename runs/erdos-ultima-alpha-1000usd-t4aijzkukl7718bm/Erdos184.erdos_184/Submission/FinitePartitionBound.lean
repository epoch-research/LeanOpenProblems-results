import Submission.UniversalBound

/-! Subadditivity over arbitrary finite edge partitions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open Critical
set_option maxHeartbeats 1600000

lemma combine_finite_families {I W : Type*} [Fintype I] [Fintype W]
    {H : SimpleGraph W} (D : I → Finset H.Subgraph) (E : I → Set (Sym2 W))
    (hD : ∀ i K, K ∈ D i → IsCycleOrEdge K.coe)
    (hp : ∀ i, Set.PairwiseDisjoint (D i : Set H.Subgraph) (fun K => K.edgeSet))
    (he : ∀ i, (⋃ K ∈ D i, K.edgeSet) = E i)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : (⋃ i, E i) = H.edgeSet) :
    ∃ F : Finset H.Subgraph,
      (∀ K ∈ F, IsCycleOrEdge K.coe) ∧ IsDecomposition H F ∧
      F.card ≤ ∑ i, (D i).card := by
  classical
  let F := Finset.univ.biUnion D
  have hsub : ∀ i K, K ∈ D i → K.edgeSet ⊆ E i := by
    intro i K hK e heK
    rw [← he i]
    exact Set.mem_iUnion.mpr ⟨K, Set.mem_iUnion.mpr ⟨hK,heK⟩⟩
  refine ⟨F, ?_, ⟨?_, ?_⟩, Finset.card_biUnion_le⟩
  · intro K hK
    obtain ⟨i,_,hK⟩ := Finset.mem_biUnion.mp hK
    exact hD i K hK
  · intro K hK L hL hne
    change K ∈ F at hK
    change L ∈ F at hL
    obtain ⟨i,_,hK⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨j,_,hL⟩ := Finset.mem_biUnion.mp hL
    by_cases hij : i = j
    · subst j
      exact hp i hK hL hne
    · exact (hE hij).mono (hsub i K hK) (hsub j L hL)
  · rw [← hcover]
    ext e
    simp only [F, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨K,⟨i,hK⟩,heK⟩
      exact ⟨i,hsub i K hK heK⟩
    · rintro ⟨i,hi⟩
      rw [← he i] at hi
      obtain ⟨K,hi⟩ := Set.mem_iUnion.mp hi
      obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp hi
      exact ⟨K,⟨i,hK⟩,heK⟩

lemma number_le_sum_partition {I : Type*} {W : Type*}
    [Fintype I] [Fintype W] (B : SimpleGraph W) (R : I → SimpleGraph W)
    (hR : ∀ i, R i ≤ B)
    (hdis : Pairwise (fun i j => Disjoint (R i).edgeSet (R j).edgeSet))
    (hcover : (⋃ i, (R i).edgeSet) = B.edgeSet) :
    number B ≤ ∑ i, number (R i) := by
  classical
  have hex : ∀ i, ∃ D : Finset (R i).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition (R i) D ∧ D.card = number (R i) := by
    intro i
    exact exists_minimum (R i)
  choose D hD hdec hc using hex
  have hlift : ∀ i, ∃ A : Finset B.Subgraph,
      (∀ H ∈ A, IsCycleOrEdge H.coe) ∧
      Set.PairwiseDisjoint (A : Set B.Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ A, H.edgeSet) = (R i).edgeSet ∧ A.card ≤ number (R i) := by
    intro i
    obtain ⟨A,hA,hp,he,hcard⟩ := lift_decomposition (hR i) (D i) (hD i) (hdec i)
    exact ⟨A,hA,hp,he,hcard.trans_eq (hc i)⟩
  choose A hA hp he hcard using hlift
  obtain ⟨F,hF,hdecF,hcF⟩ := combine_finite_families
    A (fun i => (R i).edgeSet) hA hp he hdis hcover
  exact (number_le F hF hdecF).trans
    (hcF.trans (Finset.sum_le_sum (fun i _ => hcard i)))

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.number_le_sum_partition
