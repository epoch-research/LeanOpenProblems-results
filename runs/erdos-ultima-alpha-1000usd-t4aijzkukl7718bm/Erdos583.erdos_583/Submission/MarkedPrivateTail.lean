import Submission.RunCompressionData

/-! Marked partitions on small supports and extension along a private tail.
The marked walk may be nil. -/
namespace Erdos583MarkedPrivateTailDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.MemberExpansion Erdos583Work.MarkedCycleGroups
open Erdos583Work.MarkedDouble Erdos583PrivatePathExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V]

lemma marked_on_support_of_twice_lt {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (J : SimpleGraph V) (hc : SupportConnected J) (w : V) (hw : w ∈ J.support)
    (hsize : 2*J.support.ncard < n) :
    ∃ D : Finset J.Subgraph, GoodDecomposition J D ∧ D.card ≤ ⌈(J.support.ncard : ℚ)/2⌉₊ ∧ MarkedAt D w := by
  have hcard : Fintype.card J.support=J.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,hD,hDc,a,P,hP,hPD⟩ := marked_of_twice_order_lt hsmall (J.induce J.support)
    (hc.induce_support ⟨w,hw⟩) ⟨w,hw⟩ (by rwa [hcard])
  obtain ⟨E,Q,hE,hQ,hQE,hEc⟩ := MarkedBudgets.lift_induce_marked J.support hD P hP hPD
  have hresult : ∃ E : Finset (within J J.support).Subgraph, GoodDecomposition (within J J.support) E ∧
      E.card ≤ ⌈(J.support.ncard : ℚ)/2⌉₊ ∧ MarkedAt E w := by
    refine ⟨E,hE,?_,a.val,Q,hQ,hQE⟩
    rw [hcard] at hDc
    exact hEc.trans hDc
  exact Eq.mp (congrArg (fun H : SimpleGraph V ↦
    ∃ E : Finset H.Subgraph, GoodDecomposition H E ∧
      E.card ≤ ⌈(J.support.ncard : ℚ)/2⌉₊ ∧ MarkedAt E w) (within_support_eq J)) hresult

lemma marked_on_support_of_half_fewer_edges {n : ℕ} {G₀ : SimpleGraph (Fin n)}
    (hmin : GlobalCritical.MinimalEdges G₀ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (J : SimpleGraph V) (hc : SupportConnected J) (w : V) (hw : w ∈ J.support)
    (hsize : 2*J.support.ncard=n) (hedges : 2*J.edgeSet.ncard+1 < G₀.edgeSet.ncard) :
    ∃ D : Finset J.Subgraph, GoodDecomposition J D ∧ D.card ≤ ⌈(J.support.ncard : ℚ)/2⌉₊ ∧ MarkedAt D w := by
  have hcard : Fintype.card J.support=J.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hedge : (J.induce J.support).edgeSet.ncard=J.edgeSet.ncard := by
    rw [←GlobalCritical.within_edge_ncard,within_support_eq]
  obtain ⟨D,hD,hDc,a,P,hP,hPD⟩ := GlobalCritical.marked_of_half_order_fewer_edges hmin (J.induce J.support)
    (hc.induce_support ⟨w,hw⟩) ⟨w,hw⟩ (by rwa [hcard]) (by rwa [hedge])
  obtain ⟨E,Q,hE,hQ,hQE,hEc⟩ := MarkedBudgets.lift_induce_marked J.support hD P hP hPD
  have hresult : ∃ E : Finset (within J J.support).Subgraph, GoodDecomposition (within J J.support) E ∧
      E.card ≤ ⌈(J.support.ncard : ℚ)/2⌉₊ ∧ MarkedAt E w := by
    refine ⟨E,hE,?_,a.val,Q,hQ,hQE⟩
    rw [hcard] at hDc
    exact hEc.trans hDc
  exact Eq.mp (congrArg (fun H : SimpleGraph V ↦
    ∃ E : Finset H.Subgraph, GoodDecomposition H E ∧
      E.card ≤ ⌈(J.support.ncard : ℚ)/2⌉₊ ∧ MarkedAt E w) (within_support_eq J)) hresult

lemma extend_marked_private_tail {G : SimpleGraph V} (J : SimpleGraph V) {w b : V}
    (Q : G.Walk w b) (hQ : Q.IsPath) (hwb : w ≠ b)
    (hfresh : ∀ z ∈ Q.support, z ≠ w → z ∉ J.support)
    (D : Finset J.Subgraph) (hD : GoodDecomposition J D) (hm : MarkedAt D w) :
    ∃ E : Finset (J ⊔ Q.toSubgraph.spanningCoe).Subgraph,
      GoodDecomposition _ E ∧ E.card ≤ D.card := by
  let H := J ⊔ edge w b
  let K := J ⊔ Q.toSubgraph.spanningCoe
  have hb : b ∉ J.support := hfresh b Q.end_mem_support hwb.symm
  have hwbJ : ¬J.Adj w b := fun h ↦ hb ⟨w,h.symm⟩
  have hbw : H.Adj b w := Or.inr ((edge_adj w b b w).mpr ⟨Or.inr ⟨rfl,rfl⟩,hwb.symm⟩)
  have hcoverH : H.edgeSet=insert s(b,w) J.edgeSet := by
    dsimp only [H]
    rw [edgeSet_sup,edge_edgeSet_of_ne hwb,Sym2.eq_swap]
    ext e
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  obtain ⟨a,P,hP,hPD⟩ := hm
  obtain ⟨E,hE,hEc⟩ := MarkedBudgets.append_marked_to_isolated le_sup_left hbw
    (fun z hz ↦ hb ⟨z,hz⟩) hcoverH D hD P hP hPD
  have hQK : ∀ e ∈ Q.edges, e ∈ K.edgeSet := by
    intro e he
    rw [show K=J ⊔ Q.toSubgraph.spanningCoe from rfl,edgeSet_sup]
    exact Or.inr (Q.mem_edges_toSubgraph.mpr he)
  let R := Q.transfer K hQK
  have hR : R.IsPath := hQ.transfer hQK
  have hRe : R.toSubgraph.edgeSet=Q.toSubgraph.edgeSet := by
    simp only [R,Walk.edgeSet_toSubgraph,Walk.edges_transfer]
  have hprivate : ∀ z ∈ R.support, z ≠ w → z ≠ b → z ∉ H.support := by
    intro z hz hzw hzb hzs
    obtain ⟨v,hzv⟩ := hzs
    change J.Adj z v ∨ (edge w b).Adj z v at hzv
    rcases hzv with hzv|hzv
    · exact hfresh z (by simpa only [R,Walk.support_transfer] using hz) hzw ⟨v,hzv⟩
    · rcases (edge_adj w b z v).mp hzv with ⟨⟨rfl,_⟩|⟨rfl,_⟩,_⟩
      · exact hzw rfl
      · exact hzb rfl
  have hcoverK : K.edgeSet=(H.edgeSet \ {s(w,b)}) ∪ R.toSubgraph.edgeSet := by
    dsimp only [H,K]
    rw [edgeSet_sup_edge_diff J hwb hwbJ,hRe,edgeSet_sup]
    rfl
  obtain ⟨F,hF,hFc⟩ := hE.expand_edge hbw.symm R hR hprivate hcoverK
  exact ⟨F,hF,hFc.trans hEc⟩

end Erdos583MarkedPrivateTailDevelopment
