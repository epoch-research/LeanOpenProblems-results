import Submission.MinimalBridgeRestoration

/-! Deleting a non-bridge edge incident to a vertex of degree at most two
preserves the maximum cycle-and-edge decomposition number over edge subgraphs.
Deleting a bridge lowers the hull by exactly one and preserves global
minimality. These are auxiliary reductions, not a uniform linear bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.EdgeHull
open Critical
set_option maxHeartbeats 600000
variable {V : Type*} [Fintype V]

lemma bridge_replacement_le {G R : SimpleGraph V} {e : Sym2 V}
    (hRG : R ≤ G) (hbR : R.IsBridge e) (hbG : ¬ G.IsBridge e) :
    number R ≤ value (G.deleteEdges {e}) := by
  let S := R.deleteEdges {e}
  let H := G.deleteEdges {e}
  have hSH : S ≤ H := SimpleGraph.deleteEdges_mono hRG
  obtain ⟨N,hN,hb,hr⟩ := BridgeExtension.exists_extension S H hSH
  let T := S ⊔ SimpleGraph.fromEdgeSet (N : Set (Sym2 V))
  have hTH : T ≤ H := by
    apply sup_le hSH
    intro x y hxy
    exact (hN hxy.1).1
  have hdel : T.deleteEdges (N : Set (Sym2 V)) = S := by
    ext x y
    simp only [T,SimpleGraph.deleteEdges_adj,SimpleGraph.sup_adj,
      SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hxy,hnot⟩
      rcases hxy with hxy | ⟨hxy,_⟩
      · exact hxy
      · exact (hnot hxy).elim
    · intro hxy
      exact ⟨Or.inl hxy,fun hf => (hN hf).2 hxy⟩
  have hNpos : 0 < N.card := by
    apply Finset.card_pos.mpr
    by_contra hn
    have hzero : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hTS : T = S := by simp [T,hzero]
    change T.Reachable = H.Reachable at hr
    rw [hTS] at hr
    induction e using Sym2.ind with | h a b =>
    have habR := SimpleGraph.isBridge_iff.mp hbR
    have habG : G.Adj a b := hRG habR.1
    have hre : H.Reachable a b := by
      by_contra h
      exact hbG (SimpleGraph.isBridge_iff.mpr ⟨habG,h⟩)
    have hreS : S.Reachable a b := by rwa [hr]
    exact habR.2 hreS
  have hnT := number_delete_bridges T N hb
  rw [hdel] at hnT
  have hnR := number_delete_bridge hbR
  have hnH := le_value hTH
  change number R = number S + 1 at hnR
  change number T ≤ value (G.deleteEdges {e}) at hnH
  omega

lemma value_delete_nonbridge_of_degree_le_two {G : SimpleGraph V} {v w : V}
    (hd : G.degree v ≤ 2)
    (hb : ¬ G.IsBridge s(v,w)) :
    value (G.deleteEdges {s(v,w)}) = value G := by
  apply le_antisymm (monotone (G.deleteEdges_le _))
  by_cases hz : value G = 0
  · rw [hz]
    exact Nat.zero_le _
  obtain ⟨R,hRG,hm,hn⟩ := exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
  rw [← hn]
  by_cases he : R.Adj v w
  · have hdR : R.degree v ≤ 2 := (SimpleGraph.degree_le_of_le hRG).trans hd
    exact bridge_replacement_le hRG (hm.bridge_of_degree_le_two he hdR) hb
  · apply le_value
    intro x y hxy
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hRG hxy,?_⟩
    intro h
    have hh : s(x,y) ∈ R.edgeSet := hxy
    rw [Set.mem_singleton_iff] at h
    rw [h] at hh
    exact he hh

omit [Fintype V] in
lemma delete_sup_singleton {R : SimpleGraph V} {e : Sym2 V}
    (he : e ∉ R.edgeSet) :
    (R ⊔ SimpleGraph.fromEdgeSet {e}).deleteEdges {e} = R := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj,SimpleGraph.sup_adj,
    SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨hxy,hnot⟩
    rcases hxy with hxy | ⟨hxy,_⟩
    · exact hxy
    · exact (hnot hxy).elim
  · intro hxy
    refine ⟨Or.inl hxy,?_⟩
    intro h
    have hm : s(x,y) ∈ R.edgeSet := hxy
    exact he ((Set.mem_singleton_iff.mp h) ▸ hm)

omit [Fintype V] in
lemma bridge_extension_data {G R : SimpleGraph V} {e : Sym2 V}
    (hb : G.IsBridge e) (hR : R ≤ G.deleteEdges {e}) :
    (R ⊔ SimpleGraph.fromEdgeSet {e}) ≤ G ∧
      (R ⊔ SimpleGraph.fromEdgeSet {e}).IsBridge e ∧
      (R ⊔ SimpleGraph.fromEdgeSet {e}).deleteEdges {e} = R := by
  have heG := (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hb).1
  have heR : e ∉ R.edgeSet := by
    intro he
    have hh := SimpleGraph.edgeSet_mono hR he
    rw [SimpleGraph.edgeSet_deleteEdges] at hh
    exact hh.2 (Set.mem_singleton e)
  have hTG : R ⊔ SimpleGraph.fromEdgeSet {e} ≤ G := by
    apply sup_le (hR.trans (G.deleteEdges_le _))
    intro x y hxy
    have heq := Set.mem_singleton_iff.mp hxy.1
    show s(x,y) ∈ G.edgeSet
    exact heq.symm ▸ heG
  refine ⟨hTG,?_,delete_sup_singleton heR⟩
  apply SimpleGraph.IsBridge.anti_of_mem_edgeSet hTG _ hb
  induction e using Sym2.ind with | h a b =>
  exact Or.inr ⟨Set.mem_singleton _,(show G.Adj a b from heG).ne⟩

lemma value_delete_bridge {G : SimpleGraph V} {e : Sym2 V}
    (hb : G.IsBridge e) : value G = value (G.deleteEdges {e}) + 1 := by
  apply le_antisymm
  · apply (value_le_iff G _).mpr
    intro R hRG
    by_cases he : e ∈ R.edgeSet
    · have hbR := SimpleGraph.IsBridge.anti_of_mem_edgeSet hRG he hb
      rw [number_delete_bridge hbR]
      exact Nat.add_le_add_right (le_value (SimpleGraph.deleteEdges_mono hRG)) 1
    · apply (le_value (show R ≤ G.deleteEdges {e} from ?_)).trans (Nat.le_add_right _ 1)
      intro x y hxy
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hRG hxy,?_⟩
      intro h
      have hm : s(x,y) ∈ R.edgeSet := hxy
      exact he ((Set.mem_singleton_iff.mp h) ▸ hm)
  · obtain ⟨R,hR,hn⟩ := exists_maximizer (G.deleteEdges {e})
    obtain ⟨hTG,hbT,hdel⟩ := bridge_extension_data hb hR
    have hnum := number_delete_bridge hbT
    rw [hdel,hn] at hnum
    rw [← hnum]
    exact le_value hTG

lemma Minimal.delete_bridge {G : SimpleGraph V} {e : Sym2 V}
    (hm : Minimal G) (hb : G.IsBridge e) : Minimal (G.deleteEdges {e}) := by
  intro R hR hne
  obtain ⟨hTG,hbT,hdel⟩ := bridge_extension_data hb hR
  have hneT : R ⊔ SimpleGraph.fromEdgeSet {e} ≠ G := by
    intro heq
    apply hne
    rw [← hdel,heq]
  have hmin := hm _ hTG hneT
  have hnum := number_delete_bridge hbT
  rw [hdel] at hnum
  have hnumG := number_delete_bridge hb
  omega

end Erdos184Work.EdgeHull

#print axioms Erdos184Work.EdgeHull.bridge_replacement_le
#print axioms Erdos184Work.EdgeHull.value_delete_nonbridge_of_degree_le_two

#print axioms Erdos184Work.EdgeHull.value_delete_bridge
#print axioms Erdos184Work.EdgeHull.Minimal.delete_bridge
