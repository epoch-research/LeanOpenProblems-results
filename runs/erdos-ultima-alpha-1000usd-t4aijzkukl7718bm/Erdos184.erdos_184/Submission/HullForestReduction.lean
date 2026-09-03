import Submission.LowDegreeHull

/-! A reduction of hull bounds to the part remaining after removal of bridges.
A forest bound is a certificate for a particular graph, not a bound for all graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work
open Critical
set_option maxHeartbeats 600000
variable {V W : Type*} [Fintype V] [Fintype W]

/-- The graph has a decomposition no larger than some forest contained in it. -/
def ForestBound (G : SimpleGraph V) : Prop :=
  ∃ T : SimpleGraph V, T ≤ G ∧ T.IsAcyclic ∧ number G ≤ T.edgeFinset.card

lemma ForestBound.number_le {G : SimpleGraph V} (h : ForestBound G) :
    number G ≤ Fintype.card V - 1 := by
  obtain ⟨T,_,hT,hnum⟩ := h
  exact hnum.trans (CycleCertificates.acyclic_edge_count_pred T hT)

lemma ForestBound.of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (h : ForestBound G) : ForestBound H := by
  obtain ⟨T,hTG,hT,hnum⟩ := h
  let S := T.map e.toEquiv.toEmbedding
  have hSH : S ≤ H := by
    intro x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
    exact e.toHom.map_adj (hTG hab)
  refine ⟨S,hSH,(SimpleGraph.Iso.isAcyclic_iff (SimpleGraph.Iso.map e.toEquiv T)).mp hT,?_⟩
  rw [← BlockRestriction.number_eq_of_iso e]
  have hc := SimpleGraph.card_edgeFinset_map e.toEquiv.toEmbedding T
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hc hnum ⊢
  exact hnum.trans_eq hc.symm

omit [Fintype V] in
lemma bridge_mem_of_reachable_eq {G S : SimpleGraph V} (hSG : S ≤ G)
    (hr : S.Reachable = G.Reachable) {e : Sym2 V} (hb : G.IsBridge e) :
    e ∈ S.edgeSet := by
  induction e using Sym2.ind with | h a b =>
  have hh := SimpleGraph.isBridge_iff.mp hb
  by_contra he
  have hSd : S ≤ G.deleteEdges {s(a,b)} := by
    intro x y hxy
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hSG hxy,?_⟩
    intro h
    have hm : s(x,y) ∈ S.edgeSet := hxy
    exact he ((Set.mem_singleton_iff.mp h) ▸ hm)
  have hre : S.Reachable a b := by rw [hr]; exact hh.1.reachable
  exact hh.2 (hre.mono hSd)

/-- A forest bound survives restoring edges that are all bridges. -/
lemma ForestBound.of_bridge_remainder {G K : SimpleGraph V} (hKG : K ≤ G)
    (hb : ∀ e ∈ G.edgeSet \ K.edgeSet, G.IsBridge e)
    (hK : ForestBound K) : ForestBound G := by
  obtain ⟨T,hTK,hT,hnum⟩ := hK
  obtain ⟨S,hTS,hS⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := G) (H := T) (hTK.trans hKG) hT
  have hr : S.Reachable = G.Reachable := SimpleGraph.reachable_eq_of_maximal_isAcyclic S hS
  let F := G.edgeFinset \ K.edgeFinset
  have hF : ∀ e, e ∈ F ↔ e ∈ G.edgeSet \ K.edgeSet := by
    intro e
    simp only [F,Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,Set.mem_diff]
  have hFS : F ⊆ S.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (bridge_mem_of_reachable_eq hS.prop.1 hr
      (hb e ((hF e).mp he)))
  have hdel : G.deleteEdges (F : Set (Sym2 V)) = K := by
    have he : (F : Set (Sym2 V)) = G.edgeSet \ K.edgeSet := by
      ext e
      exact hF e
    rw [he]
    exact SimpleGraph.deleteEdges_sdiff_eq_of_le hKG
  have hnumG := Critical.number_delete_bridges G F (fun e he => hb e ((hF e).mp he))
  rw [hdel] at hnumG
  have hdis : Disjoint T.edgeFinset F := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact ((hF e).mp hf).2 (SimpleGraph.edgeSet_mono hTK (SimpleGraph.mem_edgeFinset.mp he))
  have hcard : T.edgeFinset.card + F.card ≤ S.edgeFinset.card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset (SimpleGraph.edgeFinset_mono hTS) hFS)
  exact ⟨S,hS.prop.1,hS.prop.2,by omega⟩

namespace EdgeHull
/-- It suffices to certify the non-bridge remainder of each minimal core. -/
lemma value_bound_of_forest_remainders (G : SimpleGraph V)
    (h : ∀ R ≤ G, Minimal R → ∃ K : SimpleGraph V, K ≤ R ∧
      (∀ e ∈ R.edgeSet \ K.edgeSet, R.IsBridge e) ∧ ForestBound K) :
    value G ≤ Fintype.card V - 1 := by
  by_cases hz : value G = 0
  · rw [hz]
    exact Nat.zero_le _
  obtain ⟨R,hRG,hm,hn⟩ := exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
  obtain ⟨K,hKR,hb,hK⟩ := h R hRG hm
  rw [← hn]
  exact (hK.of_bridge_remainder hKR hb).number_le
end EdgeHull
end Erdos184Work

#print axioms Erdos184Work.ForestBound.of_bridge_remainder
#print axioms Erdos184Work.EdgeHull.value_bound_of_forest_remainders
