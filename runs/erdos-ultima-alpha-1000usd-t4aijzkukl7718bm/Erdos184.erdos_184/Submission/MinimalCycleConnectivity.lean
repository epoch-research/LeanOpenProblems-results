import Submission.EdgeHull

/-! In a graph globally minimal for its cycle-and-edge decomposition number,
deleting any simple cycle preserves reachability. In particular, every vertex
on a cycle has degree at least three. No uniform decomposition bound follows. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work
set_option maxHeartbeats 400000
variable {V : Type*} [Fintype V]

namespace Critical

lemma number_delete_bridge {G : SimpleGraph V} {e : Sym2 V} (hb : G.IsBridge e) :
    number G = number (G.deleteEdges {e}) + 1 := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum G
  have heG := (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hb).1
  have heD : e ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ heG
  obtain ⟨H,heD⟩ := Set.mem_iUnion.mp heD
  obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp heD
  have hs : H.coe.edgeFinset.card = 1 := by
    rcases hD H hHD with hc | hs
    · have hc' : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
        simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hc
      exact (Transversal.cycle_piece_not_bridge H hc' e heH
        (SimpleGraph.IsBridge.anti_of_mem_edgeSet H.spanningCoe_le heH hb)).elim
    · exact hs
  have hn : H.edgeSet.ncard = 1 := by
    have h := (subgraph_edge_card H).trans hs
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h
  obtain ⟨f,hf⟩ := Set.ncard_eq_one.mp hn
  have hef : e = f := by simpa only [hf,Set.mem_singleton_iff] using heH
  subst f
  exact Subfamilies.remove_single_piece_number D hD hdec hcard ⟨e,heG⟩ H hHD hf

end Critical

namespace EdgeHull
open Critical EvenCore
variable {G : SimpleGraph V}

lemma Minimal.cycleCritical (hm : Minimal G) : CycleCritical G := by
  intro u p hp
  have hlt := delete_cycle_card_lt hp
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hlt
  have hne : G \ p.toSubgraph.spanningCoe ≠ G := by
    intro h
    rw [h] at hlt
    exact (lt_irrefl _ hlt)
  have hlo := hm _ sdiff_le hne
  have hhi := number_restore_cycle hp
  omega

lemma Minimal.cycle_edge_reachable (hm : Minimal G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    {a b : V} (he : s(a,b) ∈ p.edges) :
    (G \ p.toSubgraph.spanningCoe).Reachable a b := by
  let R := G \ p.toSubgraph.spanningCoe
  let S := R ⊔ SimpleGraph.edge a b
  have hab : G.Adj a b := p.edges_subset_edgeSet he
  have heC : p.toSubgraph.spanningCoe.Adj a b := p.mem_edges_toSubgraph.mpr he
  have hnot : ¬ R.Adj a b := fun h => h.2 heC
  have hSG : S ≤ G := sup_le sdiff_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr hab))
  have hdel : S.deleteEdges {s(a,b)} = R := by
    ext x y
    simp only [S,SimpleGraph.deleteEdges_adj,SimpleGraph.sup_adj,SimpleGraph.edge_adj,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxy,hne⟩
      rcases hxy with hxy | ⟨hxy,_⟩
      · exact hxy
      · rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hne rfl).elim
        · exact (hne (Sym2.eq_swap)).elim
    · intro hxy
      refine ⟨Or.inl hxy,?_⟩
      intro heq
      have hmem : s(x,y) ∈ R.edgeSet := hxy
      rw [heq] at hmem
      exact hnot hmem
  by_contra hreach
  have hSab : S.Adj a b := Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr
    ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩)
  have hb : S.IsBridge s(a,b) := by
    apply SimpleGraph.isBridge_iff.mpr
    refine ⟨hSab,?_⟩
    change ¬ (S.deleteEdges {s(a,b)}).Reachable a b
    rwa [hdel]
  have hne : S ≠ G := by
    intro h
    have hbG : G.IsBridge s(a,b) := h ▸ hb
    exact (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hbG).2 p hp he
  have hn := number_delete_bridge hb
  rw [hdel] at hn
  have hcrit := hm.cycleCritical u p hp
  have hmin := hm S hSG hne
  change number G = number R + 1 at hcrit
  omega

/-- Deleting a cycle from a globally minimal core preserves every original
reachability relation, not merely the reachability of its incident vertices. -/
lemma Minimal.delete_cycle_reachable (hm : Minimal G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) (x y : V) :
    (G \ p.toSubgraph.spanningCoe).Reachable x y ↔ G.Reachable x y := by
  constructor
  · exact SimpleGraph.Reachable.mono sdiff_le
  · rintro ⟨q⟩
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab q ih =>
      have hr : (G \ p.toSubgraph.spanningCoe).Reachable a b := by
        by_cases he : s(a,b) ∈ p.edges
        · exact hm.cycle_edge_reachable hp he
        · exact (show (G \ p.toSubgraph.spanningCoe).Adj a b from
            ⟨hab,fun h => he (p.mem_edges_toSubgraph.mp h)⟩).reachable
      exact hr.trans ih

lemma Minimal.cycle_vertex_degree (hm : Minimal G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    3 ≤ G.degree v := by
  let C := p.toSubgraph.spanningCoe
  let R := G \ C
  have hdC : C.degree v = 2 := by
    have h := regular_two_spanning_degree p.toSubgraph (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (cycle_coe_regular G hp).2) v
    rw [if_pos (p.mem_verts_toSubgraph.mpr hv)] at h
    exact h
  obtain ⟨a,ha⟩ := (C.degree_pos_iff_exists_adj v).mp (by omega)
  have hva : v ≠ a := ha.ne
  have he : s(v,a) ∈ p.edges := p.mem_edges_toSubgraph.mp ha
  obtain ⟨q⟩ := hm.cycle_edge_reachable hp he
  have hdR : 0 < R.degree v :=
    (R.degree_pos_iff_exists_adj v).mpr ⟨q.snd,q.adj_snd (q.not_nil_of_ne hva)⟩
  have hd := degree_sdiff_add G C p.toSubgraph.spanningCoe_le v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
  change Nat.card (R.neighborSet v) + Nat.card (C.neighborSet v) = Nat.card (G.neighborSet v) at hd
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdC hdR hd ⊢
  omega

lemma Minimal.degree_two_not_on_cycle (hm : Minimal G) {v : V} (hv : G.degree v = 2)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) : v ∉ p.support := by
  intro hvp
  have h := hm.cycle_vertex_degree hp hvp
  omega

lemma Minimal.delete_cycle_connected (hm : Minimal G) (hG : G.Connected)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    (G \ p.toSubgraph.spanningCoe).Connected where
  preconnected := fun x y => (hm.delete_cycle_reachable hp x y).mpr (hG.preconnected x y)
  nonempty := hG.nonempty

/-- Every edge at a vertex of degree at most two is a bridge of a globally
minimal graph. Thus low-degree vertices cannot occur inside its cyclic blocks. -/
lemma Minimal.bridge_of_degree_le_two (hm : Minimal G) {v w : V}
    (hvw : G.Adj v w) (hd : G.degree v ≤ 2) : G.IsBridge s(v,w) := by
  apply SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem.mpr
  refine ⟨hvw,?_⟩
  intro u p hp he
  have hv := p.fst_mem_support_of_mem_edges he
  have hn := hm.cycle_vertex_degree hp hv
  omega

end EdgeHull
end Erdos184Work

#print axioms Erdos184Work.Critical.number_delete_bridge
#print axioms Erdos184Work.EdgeHull.Minimal.delete_cycle_reachable
#print axioms Erdos184Work.EdgeHull.Minimal.degree_two_not_on_cycle

#print axioms Erdos184Work.EdgeHull.Minimal.bridge_of_degree_le_two
