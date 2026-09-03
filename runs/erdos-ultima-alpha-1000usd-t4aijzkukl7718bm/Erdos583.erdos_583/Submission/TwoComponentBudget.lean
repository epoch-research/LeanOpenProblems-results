import Submission.ButterflyAcrossComponents

/-! Smaller-order budgets for graphs whose supported vertices lie in at most two components. -/
namespace Erdos583TwoComponentBudgetDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma reachable_induce_support {V : Type*} {G : SimpleGraph V} (u v : G.support)
    (h : G.Reachable u.val v.val) : (G.induce G.support).Reachable u v := by
  obtain ⟨P⟩ := h
  have hs : ∀ x ∈ P.support, x ∈ G.support := by
    by_cases hn : P.Nil
    · intro x hx
      have hx' : x=u.val := by simpa only [Walk.nil_iff_support_eq.mp hn,List.mem_singleton] using hx
      exact hx'.symm ▸ u.property
    · exact walk_support_subset_support P hn
  exact (P.induce G.support hs).reachable

lemma support_of_reachable {V : Type*} {G : SimpleGraph V} {a b : V}
    (ha : a ∈ G.support) (hab : G.Reachable a b) : b ∈ G.support := by
  by_cases he : a=b
  · exact he ▸ ha
  · exact mem_support_of_reachable (fun h ↦ he h.symm) hab.symm

lemma two_reachable_component_card {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (ha : a ∈ G.support) (hb : b ∈ G.support)
    (hcover : ∀ v ∈ G.support, G.Reachable a v ∨ G.Reachable b v) :
    Fintype.card (G.induce G.support).ConnectedComponent ≤ 2 := by
  classical
  let J := G.induce G.support
  let f : Bool → J.ConnectedComponent := fun i ↦
    if i then J.connectedComponentMk ⟨a,ha⟩ else J.connectedComponentMk ⟨b,hb⟩
  have hsur : Function.Surjective f := by
    intro C
    induction C using ConnectedComponent.ind with
    | h v =>
      rcases hcover v.val v.property with h | h
      · refine ⟨true,?_⟩
        exact ConnectedComponent.sound (reachable_induce_support ⟨a,ha⟩ v h)
      · refine ⟨false,?_⟩
        exact ConnectedComponent.sound (reachable_induce_support ⟨b,hb⟩ v h)
  simpa only [Fintype.card_bool] using Fintype.card_le_of_surjective f hsur

lemma smaller_orders_two_components {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hsize : Fintype.card V < n)
    (hcomp : Fintype.card G.ConnectedComponent ≤ 2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V+2 := by
  classical
  obtain ⟨D,hD,hDc⟩ := ComponentBudget.partition_components G (fun C ↦ ⌈(C.supp.ncard : ℚ)/2⌉₊) (by
    intro C
    exact hsmall.on_induce G C.supp
      ((C.supp.ncard_le_card.trans_eq Nat.card_eq_fintype_card).trans_lt hsize) C.connected_toSimpleGraph)
  have hc (C : G.ConnectedComponent) : 2*⌈(C.supp.ncard : ℚ)/2⌉₊ ≤ C.supp.ncard+1 := by
    rw [ceil_half]; omega
  have hs : ∑ C : G.ConnectedComponent, 2*⌈(C.supp.ncard : ℚ)/2⌉₊ ≤ Fintype.card V+2 := by
    calc
      _ ≤ ∑ C : G.ConnectedComponent, (C.supp.ncard+1) := Finset.sum_le_sum (fun C _ ↦ hc C)
      _ = Fintype.card V+Fintype.card G.ConnectedComponent := by
        rw [Finset.sum_add_distrib,ComponentBudget.sum_component_orders]
        simp
      _ ≤ _ := by omega
  rw [←Finset.mul_sum] at hs
  exact ⟨D,hD,(Nat.mul_le_mul_left 2 hDc).trans hs⟩

lemma smaller_orders_two_support_components {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hsize : G.support.ncard < n)
    (hcomp : Fintype.card (G.induce G.support).ConnectedComponent ≤ 2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ G.support.ncard+2 := by
  classical
  have hc : Fintype.card G.support=G.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hsize' : Fintype.card G.support < n := by omega
  obtain ⟨D,hD,hDc⟩ := smaller_orders_two_components (V := G.support) hsmall
    (G.induce G.support) hsize' (by simpa only [←Nat.card_eq_fintype_card] using hcomp)
  obtain ⟨E,hE,hEc⟩ := hD.lift_induce_support G
  exact ⟨E,hE,(Nat.mul_le_mul_left 2 hEc).trans (by simpa only [hc] using hDc)⟩

lemma disconnected_two_reachable {V : Type*} {G : SimpleGraph V} {a b : V}
    (hcover : ∀ v ∈ G.support, G.Reachable a v ∨ G.Reachable b v)
    (hn : ¬SupportConnected G) : a ∈ G.support ∧ b ∈ G.support ∧ ¬G.Reachable a b := by
  classical
  obtain ⟨u,hu,v,hv,huv⟩ : ∃ u ∈ G.support, ∃ v ∈ G.support, ¬G.Reachable u v := by
    unfold SupportConnected at hn
    push_neg at hn
    exact hn
  have hab : ¬G.Reachable a b := by
    intro hab
    rcases hcover u hu with ha | hb <;> rcases hcover v hv with ha' | hb'
    · exact huv (ha.symm.trans ha')
    · exact huv (ha.symm.trans (hab.trans hb'))
    · exact huv (hb.symm.trans (hab.symm.trans ha'))
    · exact huv (hb.symm.trans hb')
  have hboth : (G.Reachable a u ∧ G.Reachable b v) ∨ (G.Reachable b u ∧ G.Reachable a v) := by
    rcases hcover u hu with ha | hb <;> rcases hcover v hv with ha' | hb'
    · exact (huv (ha.symm.trans ha')).elim
    · exact Or.inl ⟨ha,hb'⟩
    · exact Or.inr ⟨hb,ha'⟩
    · exact (huv (hb.symm.trans hb')).elim
  rcases hboth with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · exact ⟨support_of_reachable hu ha.symm,support_of_reachable hv hb.symm,hab⟩
  · exact ⟨support_of_reachable hv ha.symm,support_of_reachable hu hb.symm,hab⟩

end Erdos583TwoComponentBudgetDevelopment
