import Submission.CollisionEndpointLabels

/-! Prescribed near-complete pairs from a repaired endpoint-slot map,
independent of the orientation of the selected repeated label. -/
namespace Erdos583CollisionCorePairsDevelopment
open SimpleGraph Erdos583Work
open Erdos583NearCompletePairsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma near_complete_repaired_pairs {V : Type*} [Fintype V] {k : ℕ}
    (u v : V) (huv : u ≠ v) (a b : Fin k → V) (i : Fin k) (c : Bool)
    (hi : (if c then a i else b i)=v) (hab : a i ≠ b i)
    (he : Function.Bijective (fun z : Fin k × Bool ↦
      if z=(i,c) then u else if z.2 then a z.1 else b z.1)) :
    ∃ q : ∀ l, ((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).Walk (a l) (b l),
      (∀ l, (q l).IsPath) ∧
      Pairwise (fun l m ↦ Disjoint (q l).toSubgraph.edgeSet (q m).toSubgraph.edgeSet) ∧
      (⋃ l, (q l).toSubgraph.edgeSet)=((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).edgeSet := by
  classical
  cases c
  · have hbi : b i=v := hi
    have hai : a i ≠ v := by simpa only [←hbi] using hab
    have he' : Function.Bijective (fun z : Fin k × Bool ↦
        if z.2 then (if z.1=i then u else b z.1) else a z.1) := by
      apply (Fintype.bijective_iff_surjective_and_card _).mpr
      constructor
      · intro w
        obtain ⟨⟨j,c⟩,hj⟩ := he.surjective w
        refine ⟨(j,!c),?_⟩
        cases c <;> simpa using hj
      · exact Fintype.card_of_bijective he
    obtain ⟨p,hp,hd,hc⟩ := near_complete_prescribed_pairs u v huv b a i hbi hai he'
    refine ⟨fun l ↦ (p l).reverse,?_,?_,?_⟩
    · intro l; exact (hp l).reverse
    · simpa only [Walk.toSubgraph_reverse] using hd
    · simpa only [Walk.toSubgraph_reverse] using hc
  · have hai : a i=v := hi
    have hbi : b i ≠ v := by simpa only [←hai] using Ne.symm hab
    have he' : Function.Bijective (fun z : Fin k × Bool ↦
        if z.2 then (if z.1=i then u else a z.1) else b z.1) := by
      convert he using 1
      funext z
      rcases z with ⟨j,c⟩
      cases c <;> simp
    exact near_complete_prescribed_pairs u v huv a b i hai hbi he'

end Erdos583CollisionCorePairsDevelopment
