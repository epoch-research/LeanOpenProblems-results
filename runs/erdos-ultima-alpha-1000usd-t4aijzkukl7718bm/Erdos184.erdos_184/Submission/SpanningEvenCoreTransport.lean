import Submission.GraphCircuitCode
import Submission.CircuitTransport

/-! Adding isolated vertices preserves the even-core notions and the cycle
number of an even graph. These transport lemmas are not a uniform bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SpanningEvenCoreTransport
open Critical EvenCore Rigidity GraphCircuitCode Erdos184Serial
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {S : Set V}

lemma spanning_even (H : SimpleGraph S) (he : ∀ v, Even (H.degree v)) :
    ∀ v, Even (H.spanningCoe.degree v) := by
  intro v
  by_cases hv : v ∈ S
  · have hd := Vertex.spanningCoe_degree H ⟨v,hv⟩
    have hh := he ⟨v,hv⟩
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hh ⊢
    rwa [hd]
  · have hz : H.spanningCoe.degree v = 0 :=
      (SimpleGraph.degree_eq_zero_iff_notMem_support _ _).mpr
        (fun h => hv (Vertex.spanningCoe_support_subset H h))
    rw [hz]
    exact Even.zero

lemma spanning_code_valid (H : SimpleGraph S) (t : Finset (Sym2 S)) :
    (code H).valid t ↔
      (code H.spanningCoe).valid (t.map (Function.Embedding.subtype (· ∈ S)).sym2Map) := by
  constructor
  · rintro ⟨R,hR,he,rfl⟩
    refine ⟨R.spanningCoe,?_,?_,?_⟩
    · intro x y hxy
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
      exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨a,b,hR hab,rfl,rfl⟩
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using spanning_even R he
    · simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using
        SimpleGraph.edgeFinset_map (Function.Embedding.subtype (· ∈ S)) R
  · rintro ⟨R,hR,he,ht⟩
    have hs : R.support ⊆ S := (SimpleGraph.support_mono hR).trans
      (Vertex.spanningCoe_support_subset H)
    have hRH : R.induce S ≤ H := by
      intro x y hxy
      have hh := hR hxy
      change H.spanningCoe.Adj x.val y.val at hh
      have hh' : (H.spanningCoe.induce S).Adj x y := hh
      simpa only [SimpleGraph.induce_spanningCoe] using hh'
    have heR : ∀ x, Even ((R.induce S).degree x) := by
      intro x
      have hd := SimpleGraph.degree_induce_of_support_subset hs x
      have hh := he x.val
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hh ⊢
      rwa [hd]
    refine ⟨R.induce S,hRH,heR,?_⟩
    apply Finset.map_injective (Function.Embedding.subtype (· ∈ S)).sym2Map
    rw [SimpleGraph.map_edgeFinset_induce_of_support_subset hs,ht]

lemma spanning_number (H : SimpleGraph S) (he : ∀ v, Even (H.degree v)) :
    number H.spanningCoe = number H := by
  have hHe : ∀ v, Even (H.spanningCoe.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using spanning_even H he
  have hh := (hasNumber_map_iff (Function.Embedding.subtype (· ∈ S)).sym2Map
    (spanning_code_valid H) H.edgeFinset (number H)).mpr (hasNumber le_rfl he)
  have hc := SimpleGraph.edgeFinset_map (Function.Embedding.subtype (· ∈ S)) H
  rw [← hc] at hh
  have hi := hasNumber_iff (G := H.spanningCoe) (R := H.spanningCoe) le_rfl (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hHe) (number H)
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hh hi
  exact hi.mp hh

lemma spanning_minimal_iff (H : SimpleGraph S) (he : ∀ v, Even (H.degree v)) :
    EvenMinimal H.spanningCoe ↔ EvenMinimal H := by
  have hHe : ∀ v, Even (H.spanningCoe.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using spanning_even H he
  have hh := minimalCore_map_iff (Function.Embedding.subtype (· ∈ S)).sym2Map
    (spanning_code_valid H) H.edgeFinset (number H)
  have hc := SimpleGraph.edgeFinset_map (Function.Embedding.subtype (· ∈ S)) H
  rw [← hc] at hh
  have hi := minimalCore_iff (G := H.spanningCoe) (R := H.spanningCoe) le_rfl (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hHe) (number H)
  have hj := minimalCore_iff (G := H) (R := H) le_rfl he (number H)
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hh hi hj
  rw [hi,hj] at hh
  simpa only [spanning_number H he,eq_self_iff_true,and_true] using hh

end Erdos184Work.SpanningEvenCoreTransport
#print axioms Erdos184Work.SpanningEvenCoreTransport.spanning_number
#print axioms Erdos184Work.SpanningEvenCoreTransport.spanning_minimal_iff
