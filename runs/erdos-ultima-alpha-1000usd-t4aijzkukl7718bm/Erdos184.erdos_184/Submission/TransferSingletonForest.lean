import Submission.SingletonStarStructure

/-! Transfer along a best singleton edge: the singleton forest can be carried
through the move, with its size unchanged and the sender made a leaf.
This does not prove a decomposition-number or hull comparison. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.Compression
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma reachable_of_adj_reachable {G H : SimpleGraph V}
    (h : ∀ x y, G.Adj x y → H.Reachable x y) {x y : V} (hp : G.Reachable x y) :
    H.Reachable x y := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih => exact (h x y hxy).trans ih

lemma transfer_adj_reachable {G : SimpleGraph V} {u v x y : V}
    (huv : G.Adj u v) (hxy : (transfer G u v).Adj x y) : G.Reachable x y := by
  rcases hxy with hxy | ⟨_,hxy | hxy⟩
  · exact hxy.1.reachable
  · rcases hxy with ⟨rfl,_,hvy,_⟩
    exact huv.reachable.trans hvy.reachable
  · rcases hxy with ⟨rfl,_,hvx,_⟩
    exact (huv.reachable.trans hvx.reachable).symm

lemma adj_reachable_transfer {G : SimpleGraph V} {u v x y : V}
    (huv : G.Adj u v) (hxy : G.Adj x y) : (transfer G u v).Reachable x y := by
  let M := SimpleGraph.fromRel
    (fun x y => x = v ∧ y ≠ u ∧ G.Adj v y ∧ ¬ G.Adj u y)
  have hpair : (transfer G u v).Adj u v := (transfer_adj_pair G u v).mpr huv
  by_cases hm : M.Adj x y
  · rcases hm with ⟨_,hm | hm⟩
    · rcases hm with ⟨hxv,hyu,hvy,_⟩
      subst x
      have hy : (transfer G u v).Adj u y :=
        (transfer_adj_left G huv.ne hyu hvy.ne.symm).mpr (Or.inr hvy)
      exact hpair.symm.reachable.trans hy.reachable
    · rcases hm with ⟨hyv,hxu,hvx,_⟩
      subst y
      have hx : (transfer G u v).Adj u x :=
        (transfer_adj_left G huv.ne hxu hvx.ne.symm).mpr (Or.inr hvx)
      exact (hpair.symm.reachable.trans hx.reachable).symm
  · exact (show (transfer G u v).Adj x y from Or.inl ⟨hxy,hm⟩).reachable

lemma transfer_reachable {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    (transfer G u v).Reachable = G.Reachable := by
  funext x y
  apply propext
  constructor
  · exact reachable_of_adj_reachable (fun _ _ h => transfer_adj_reachable huv h)
  · exact reachable_of_adj_reachable (fun _ _ h => adj_reachable_transfer huv h)

lemma transfer_connected {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (hc : G.Connected) : (transfer G u v).Connected where
  preconnected := by
    intro x y
    rw [transfer_reachable huv]
    exact hc.preconnected x y
  nonempty := hc.nonempty

lemma transfer_tree {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (ht : G.IsTree) : (transfer G u v).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨transfer_connected huv ht.isConnected,?_⟩
  have hc := ht.card_edgeFinset
  have he := transfer_edge_card G u v
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hc he
  omega

lemma transfer_acyclic {F : SimpleGraph V} {u v : V}
    (huv : F.Adj u v) (ha : F.IsAcyclic) : (transfer F u v).IsAcyclic := by
  letI : Nonempty V := ⟨u⟩
  obtain ⟨T,hFT,hTm⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := (⊤ : SimpleGraph V)) le_top ha
  have ht : T.IsTree :=
    (SimpleGraph.connected_top.maximal_le_isAcyclic_iff_isTree le_top).mp hTm
  exact (transfer_tree (hFT huv) ht).IsAcyclic.anti (transfer_mono hFT u v)

end Erdos184Work.Compression

namespace Erdos184Work.SingletonExchange
open Compression
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma Best.singleton_neighbor_private {G F : SimpleGraph V} (hb : Best G F)
    {u v w : V} (huv : F.Adj u v) (hvw : F.Adj v w) (hwu : w ≠ u) :
    ¬ G.Adj u w := by
  intro huw
  have hf := hb.reachable_induced (huv.reachable.trans hvw.reachable) huw
  exact acyclic_no_triangle hb.1.acyclic huv hvw hf

lemma Best.transfer_even_remainder {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v) :
    transfer G u v \ transfer F u v = transfer (G \ F) u v := by
  have hleft (w : V) (hwu : w ≠ u) (hwv : w ≠ v) :
      (transfer G u v \ transfer F u v).Adj u w ↔
        (transfer (G \ F) u v).Adj u w := by
    rw [SimpleGraph.sdiff_adj, transfer_adj_left G huv.ne hwu hwv,
      transfer_adj_left F huv.ne hwu hwv,
      transfer_adj_left (G \ F) huv.ne hwu hwv]
    simp only [SimpleGraph.sdiff_adj]
    have h1 := hb.singleton_neighbor_private (w := w) huv.symm
    have h2 := hb.singleton_neighbor_private (w := w) huv
    constructor
    · rintro ⟨h,hf⟩
      rcases h with h | h
      · exact Or.inl ⟨h,fun hf' => hf (Or.inl hf')⟩
      · exact Or.inr ⟨h,fun hf' => hf (Or.inr hf')⟩
    · rintro (⟨h,hf⟩ | ⟨h,hf⟩)
      · refine ⟨Or.inl h,?_⟩
        rintro (hu | hv)
        · exact hf hu
        · exact h2 hv hwu h
      · refine ⟨Or.inr h,?_⟩
        rintro (hu | hv)
        · exact h1 hu hwv h
        · exact hf hv
  have hright (w : V) (hwu : w ≠ u) (hwv : w ≠ v) :
      (transfer G u v \ transfer F u v).Adj v w ↔
        (transfer (G \ F) u v).Adj v w := by
    rw [SimpleGraph.sdiff_adj, transfer_adj_right G huv.ne hwu hwv,
      transfer_adj_right F huv.ne hwu hwv,
      transfer_adj_right (G \ F) huv.ne hwu hwv]
    simp only [SimpleGraph.sdiff_adj]
    constructor
    · rintro ⟨⟨hv,hu⟩,_⟩
      exact ⟨⟨hv,fun hf => hb.singleton_neighbor_private huv hf hwu hu⟩,
        ⟨hu,fun hf => hb.singleton_neighbor_private huv.symm hf hwv hv⟩⟩
    · rintro ⟨⟨hv,hfv⟩,⟨hu,_⟩⟩
      exact ⟨⟨hv,hu⟩,fun h => hfv h.1⟩
  have hpair : (transfer G u v \ transfer F u v).Adj u v ↔
      (transfer (G \ F) u v).Adj u v := by
    simp only [SimpleGraph.sdiff_adj,transfer_adj_pair]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hxu : x = u
  · subst x
    by_cases hyv : y = v
    · subst y
      exact hpair
    · exact hleft y (Ne.symm hxy) hyv
  by_cases hxv : x = v
  · subst x
    by_cases hyu : y = u
    · subst y
      simpa only [SimpleGraph.adj_comm] using hpair
    · exact hright y hyu (Ne.symm hxy)
  by_cases hyu : y = u
  · subst y
    simpa only [SimpleGraph.adj_comm] using hleft x hxu hxv
  by_cases hyv : y = v
  · subst y
    simpa only [SimpleGraph.adj_comm] using hright x hxu hxv
  simp only [SimpleGraph.sdiff_adj,
    transfer_adj_away G hxu hxv hyu hyv, transfer_adj_away F hxu hxv hyu hyv,
    transfer_adj_away (G \ F) hxu hxv hyu hyv]

lemma Best.transfer_split {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v) :
    transfer (G \ F) u v ⊔ transfer F u v = transfer G u v ∧
      Disjoint (transfer (G \ F) u v) (transfer F u v) := by
  rw [← hb.transfer_even_remainder huv]
  refine ⟨sdiff_sup_cancel (transfer_mono hb.1.1 u v),?_⟩
  rw [disjoint_iff]
  ext x y
  simp only [SimpleGraph.inf_adj,SimpleGraph.sdiff_adj,SimpleGraph.bot_adj]
  tauto

lemma Best.transferred_sender_leaf {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v) :
    (transfer F u v).neighborSet v = {u} := by
  ext w
  constructor
  · intro hw
    change (transfer F u v).Adj v w at hw
    by_contra hwu
    have hwv : w ≠ v := hw.ne.symm
    obtain ⟨hvw,huw⟩ := (transfer_adj_right F huv.ne hwu hwv).mp hw
    exact acyclic_no_triangle hb.1.acyclic huv hvw huw
  · intro hw
    have hwu : w = u := hw
    subst w
    exact ((transfer_adj_pair F u v).mpr huv).symm

lemma Best.transferred_forest {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v) :
    transfer F u v ≤ transfer G u v ∧
      (transfer F u v).IsAcyclic ∧
      (transfer F u v).edgeFinset.card = F.edgeFinset.card ∧
      Nat.card ((transfer F u v).neighborSet v) = 1 := by
  refine ⟨transfer_mono hb.1.1 u v, transfer_acyclic huv hb.1.acyclic,
    transfer_edge_card F u v,?_⟩
  rw [hb.transferred_sender_leaf huv]
  simp

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.Compression.transfer_acyclic
#print axioms Erdos184Work.SingletonExchange.Best.transferred_forest

#print axioms Erdos184Work.SingletonExchange.Best.transfer_split
