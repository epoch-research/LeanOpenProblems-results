import Submission.MinimalBridgeRestoration

/-! Edge-hull maximizers preserve reachability. Cycle deletion followed by
minimal-core extraction therefore gives a connected descent for globally
edge-minimal graphs. No uniform bound on the length of this descent is claimed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.EdgeHull
open Critical
set_option maxHeartbeats 600000
variable {V : Type*} [Fintype V]

lemma maximizer_reachable {G R : SimpleGraph V} (hRG : R ≤ G)
    (hn : number R = value G) : R.Reachable = G.Reachable := by
  obtain ⟨N,hN,hb,hr⟩ := BridgeExtension.exists_extension R G hRG
  let T := R ⊔ SimpleGraph.fromEdgeSet (N : Set (Sym2 V))
  have hTG : T ≤ G := by
    apply sup_le hRG
    intro x y hxy
    exact (hN hxy.1).1
  have hdel : T.deleteEdges (N : Set (Sym2 V)) = R := by
    ext x y
    simp only [T,SimpleGraph.deleteEdges_adj,SimpleGraph.sup_adj,
      SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hxy,hnot⟩
      exact hxy.elim id (fun h => (hnot h.1).elim)
    · intro hxy
      exact ⟨Or.inl hxy,fun h => (hN h).2 hxy⟩
  have hnum := number_delete_bridges T N hb
  rw [hdel] at hnum
  have hle := le_value hTG
  have hz : N.card = 0 := by omega
  have he : N = ∅ := Finset.card_eq_zero.mp hz
  simpa only [he,Finset.coe_empty,SimpleGraph.fromEdgeSet_empty,sup_bot_eq] using hr

lemma maximizer_connected {G R : SimpleGraph V} (hRG : R ≤ G)
    (hn : number R = value G) (hG : G.Connected) : R.Connected where
  preconnected := by
    intro x y
    rw [maximizer_reachable hRG hn]
    exact hG.preconnected x y
  nonempty := hG.nonempty

lemma exists_minimal_maximizer_all (G : SimpleGraph V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ Minimal R ∧ number R = value G := by
  by_cases hz : value G = 0
  · refine ⟨⊥,bot_le,?_,?_⟩
    · intro R hR hne
      exact (hne (le_bot_iff.mp hR)).elim
    · have hle := le_value (bot_le : (⊥ : SimpleGraph V) ≤ G)
      omega
  · exact exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)

lemma exists_minimal_maximizer_reachable (G : SimpleGraph V) :
    ∃ R : SimpleGraph V, R ≤ G ∧ Minimal R ∧ number R = value G ∧
      R.Reachable = G.Reachable := by
  obtain ⟨R,hR,hm,hn⟩ := exists_minimal_maximizer_all G
  exact ⟨R,hR,hm,hn,maximizer_reachable hR hn⟩

lemma Minimal.cycle_cofactor_hull {G : SimpleGraph V} (hm : Minimal G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    value (G \ p.toSubgraph.spanningCoe) = number (G \ p.toSubgraph.spanningCoe) := by
  apply le_antisymm _ (number_le_value _)
  apply (value_le_iff _ _).mpr
  intro R hR
  have hc := hm.cycleCritical u p hp
  have hne : R ≠ G := by
    intro heq
    have hle : G ≤ G \ p.toSubgraph.spanningCoe := heq ▸ hR
    have he := p.toSubgraph_adj_snd hp.not_nil
    exact (hle (p.adj_snd hp.not_nil)).2 he
  have hlt := hm R (hR.trans sdiff_le) hne
  omega

/-- Every simple cycle of a globally minimal graph admits a smaller minimal
core after deletion, with unit loss and exactly the same reachability. -/
lemma Minimal.cycle_descent {G : SimpleGraph V} (hm : Minimal G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∃ R : SimpleGraph V, R ≤ G \ p.toSubgraph.spanningCoe ∧ Minimal R ∧
      number R + 1 = number G ∧ R.Reachable = G.Reachable := by
  obtain ⟨R,hR,hmin,hn,hr⟩ := exists_minimal_maximizer_reachable
    (G \ p.toSubgraph.spanningCoe)
  have hc := hm.cycleCritical u p hp
  rw [hm.cycle_cofactor_hull hp] at hn
  refine ⟨R,hR,hmin,by omega,?_⟩
  exact hr.trans (funext fun x => funext fun y => propext (hm.delete_cycle_reachable hp x y))

end Erdos184Work.EdgeHull
#print axioms Erdos184Work.EdgeHull.maximizer_reachable
#print axioms Erdos184Work.EdgeHull.exists_minimal_maximizer_reachable
#print axioms Erdos184Work.EdgeHull.Minimal.cycle_descent
