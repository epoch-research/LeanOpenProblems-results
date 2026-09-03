import Submission.TransferSingletonForest

/-! A parity-corrected forest after transfer along a best singleton edge.
The forest is not asserted to be optimal; no hull monotonicity follows here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Compression
set_option maxHeartbeats 600000
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma sdiff_delete_pair_delete {G F : SimpleGraph V} {u v : V}
    (huv : F.Adj u v) :
    (G \ F.deleteEdges {s(u,v)}).deleteEdges {s(u,v)} = G \ F := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sdiff_adj]
  have he : s(x,y) ∈ ({s(u,v)} : Set (Sym2 V)) → F.Adj x y := by
    intro h
    change s(x,y) ∈ F.edgeSet
    rw [Set.mem_singleton_iff.mp h]
    exact huv
  tauto

lemma transfer_even_of_even_private {E : SimpleGraph V} {u v : V}
    (huv : u ≠ v) (he : ∀ w, Even (Nat.card (E.neighborSet w)))
    (hp : Even (privateNeighbors E u v).card) :
    ∀ w, Even (Nat.card ((transfer E u v).neighborSet w)) := by
  have hl := transfer_degree_left (G := E) huv
  have hr := transfer_degree_right (G := E) huv
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hl hr
  intro w
  have hp' := Nat.even_iff.mp hp
  have hw := Nat.even_iff.mp (he w)
  rw [Nat.even_iff]
  by_cases hwu : w = u
  · subst w
    omega
  by_cases hwv : w = v
  · subst w
    omega
  have ho := transfer_degree_other (G := E) hwu hwv
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at ho
  omega

lemma Best.transfer_delete_pair_even {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v)
    (hp : Odd (privateNeighbors (G \ F) u v).card) :
    ∀ w, Even (Nat.card
      ((transfer G u v \ (transfer F u v).deleteEdges {s(u,v)}).neighborSet w)) := by
  let R := transfer G u v \ (transfer F u v).deleteEdges {s(u,v)}
  have hF : (transfer F u v).Adj u v := (transfer_adj_pair F u v).mpr huv
  have hG : (transfer G u v).Adj u v := (transfer_adj_pair G u v).mpr (hb.1.1 huv)
  have hR : R.Adj u v := by
    exact ⟨hG, by simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
      not_true_eq_false, and_false, not_false_eq_true]⟩
  have hd : R.deleteEdges {s(u,v)} = transfer (G \ F) u v := by
    rw [sdiff_delete_pair_delete hF, hb.transfer_even_remainder huv]
  have hl := transfer_degree_left (G := G \ F) huv.ne
  have hr := transfer_degree_right (G := G \ F) huv.ne
  have hdl := delete_edge_degree_left hR
  have hdr := delete_edge_degree_right hR
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hl hr hdl hdr
  rw [hd] at hdl hdr
  have hp' := Nat.odd_iff.mp hp
  intro w
  change Even (Nat.card (R.neighborSet w))
  have he := Nat.even_iff.mp (hb.1.2.1 w)
  rw [Nat.even_iff]
  by_cases hwu : w = u
  · subst w
    omega
  by_cases hwv : w = v
  · subst w
    omega
  have ho := transfer_degree_other (G := G \ F) hwu hwv
  have hdo := delete_edge_degree_other (G := R) hwu hwv
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at ho hdo
  rw [hd] at hdo
  omega

lemma Best.transferred_delete_pair_size {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v) :
    Nat.card ((transfer F u v).deleteEdges {s(u,v)}).edgeSet + 1 =
        Nat.card F.edgeSet ∧
      Nat.card (((transfer F u v).deleteEdges {s(u,v)}).neighborSet v) = 0 := by
  have hF : (transfer F u v).Adj u v := (transfer_adj_pair F u v).mpr huv
  have hFT := hb.transferred_forest huv
  constructor
  · have he : Nat.card (((transfer F u v).deleteEdges {s(u,v)}).edgeSet) + 1 =
        Nat.card (transfer F u v).edgeSet := by
      simp only [SimpleGraph.edgeSet_deleteEdges, Nat.card_coe_set_eq]
      exact Set.ncard_diff_singleton_add_one hF
    have hc := hFT.2.2.1
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc
    omega
  · have hd := delete_edge_degree_right hF
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
    have hv := hFT.2.2.2
    omega

/-- The natural transferred forest, or that forest with its joining edge
removed, has an even cofactor. Its size never increases and the sender is
incident to at most one forest edge. This does not assert optimality. -/
lemma Best.exists_transferred_parity_forest {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v) :
    ∃ J : SimpleGraph V,
      J ≤ transfer F u v ∧ J ≤ transfer G u v ∧ J.IsAcyclic ∧
      (∀ w, Even (Nat.card ((transfer G u v \ J).neighborSet w))) ∧
      Nat.card J.edgeSet ≤ Nat.card F.edgeSet ∧
      Nat.card (J.neighborSet v) ≤ 1 := by
  have hFT := hb.transferred_forest huv
  by_cases hp : Even (privateNeighbors (G \ F) u v).card
  · refine ⟨transfer F u v, le_rfl, hFT.1, hFT.2.1, ?_, ?_, hFT.2.2.2.le⟩
    · rw [hb.transfer_even_remainder huv]
      exact transfer_even_of_even_private huv.ne hb.1.2.1 hp
    · have hc := hFT.2.2.1
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc.le
  · let J := (transfer F u v).deleteEdges {s(u,v)}
    have hJ : J ≤ transfer F u v := (transfer F u v).deleteEdges_le _
    have hc : J.edgeFinset.card ≤ F.edgeFinset.card := by
      calc
        _ ≤ (transfer F u v).edgeFinset.card :=
          Finset.card_le_card (SimpleGraph.edgeFinset_mono hJ)
        _ = _ := hFT.2.2.1
    have hjv : Nat.card (J.neighborSet v) ≤ 1 := by
      have hdeg : J.degree v ≤ (transfer F u v).degree v := SimpleGraph.degree_le_of_le hJ
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg
      exact hdeg.trans hFT.2.2.2.le
    refine ⟨J, hJ, hJ.trans hFT.1, hFT.2.1.anti hJ, ?_, ?_, hjv⟩
    · exact hb.transfer_delete_pair_even huv (Nat.not_even_iff_odd.mp hp)
    · simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.Best.transfer_delete_pair_even
#print axioms Erdos184Work.SingletonExchange.Best.exists_transferred_parity_forest

#print axioms Erdos184Work.SingletonExchange.Best.transferred_delete_pair_size
