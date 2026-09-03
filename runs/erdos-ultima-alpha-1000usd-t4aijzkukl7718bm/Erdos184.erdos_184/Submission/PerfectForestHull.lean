import Submission.MinimumParityForest

/-! Perfect forests give an additive hull gain for even graphs of even order.
This is not a fixed relative gain in the decomposition number. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MinimumParity
open Critical
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma Minimum.cycle_outside_two {G F H : SimpleGraph V} (hm : Minimum G F)
    (hHG : H ≤ G) {u : V} (p : H.Walk u u) (hp : p.IsCycle) :
    2 ≤ Nat.card (p.toSubgraph.spanningCoe \ F).edgeSet := by
  let C := p.toSubgraph.spanningCoe
  have he : ∀ v, Even (Nat.card (C.neighborSet v)) := by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using cycle_spanning_even H hp v
  have hb := hm.even_balance C (p.toSubgraph.spanningCoe_le.trans hHG) he
  have hs := sdiff_add_inf_card C F
  rw [inf_comm C F] at hs
  have hc := cycle_edge_count H hp
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hc
  change Nat.card C.edgeSet = p.length at hc
  have hl := hp.three_le_length
  change 2 ≤ Nat.card (C \ F).edgeSet
  omega

lemma Minimum.even_repair_bound {G F H : SimpleGraph V} (hm : Minimum G F)
    (hHG : H ≤ G) (he : ∀ v, Even (Nat.card (H.neighborSet v))) :
    2 * number H ≤ (H \ F).edgeFinset.card := by
  apply StarDeletion.even_number_outside_two he
  intro K hK
  obtain ⟨v⟩ := hK.1.nonempty
  obtain ⟨p,hp,hpK⟩ := LongRing.regular_cycle_walk_at K hK.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hK.2) v.val v.property
  have hb := hm.cycle_outside_two hHG p hp
  rw [hpK] at hb
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hb

lemma all_odd_singleton_bound {G : SimpleGraph V}
    (ho : ∀ v, Odd (Nat.card (G.neighborSet v)))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) :
    Fintype.card V ≤ 2 * (edgePieces D).card := by
  let F := subfamilyGraph (edgePieces D)
  have hd (v : V) : 1 ≤ F.degree v :=
    ParityDegreeLower.singleton_degree_pos D hD hdec (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using ho v)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hd v)
  rw [F.sum_degrees_eq_twice_card_edges] at hs
  have hc := edgePieces_graph_card D hdec
  change F.edgeFinset.card = (edgePieces D).card at hc
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs hc
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,hc] using hs

/-- On even preconnected graphs of even order, the hull exceeds the minimum
number by at least one quarter of the order. This remains an additive bound. -/
lemma perfect_forest_hull_boost (G : SimpleGraph V) (hc : G.Preconnected)
    (hn : Even (Fintype.card V))
    (he : ∀ v, Even (Nat.card (G.neighborSet v))) :
    4 * number G + Fintype.card V ≤ 4 * EdgeHull.value G := by
  obtain ⟨F,hm,_,ho,_⟩ := exists_perfect_forest G hc hn
  have hodd (v : V) : Odd (Nat.card ((G \ F).neighborSet v)) := by
    have hd := degree_sdiff_add G F hm.1 v
    have hg := Nat.even_iff.mp (he v)
    have hf := Nat.odd_iff.mp (ho v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
    rw [Nat.odd_iff]
    omega
  have hb := StarDeletion.delete_with_repair (b := Fintype.card V / 2) hm.1 he
    (fun T hTG hT => hm.even_repair_bound hTG hT) (by
      intro D hD hdec
      have hs := all_odd_singleton_bound hodd D hD hdec
      omega)
  have hh := EdgeHull.le_value (sdiff_le : G \ F ≤ G)
  have hn' := Nat.even_iff.mp hn
  omega

end Erdos184Work.MinimumParity
#print axioms Erdos184Work.MinimumParity.exists_perfect_forest
#print axioms Erdos184Work.MinimumParity.Minimum.even_repair_bound
#print axioms Erdos184Work.MinimumParity.perfect_forest_hull_boost
