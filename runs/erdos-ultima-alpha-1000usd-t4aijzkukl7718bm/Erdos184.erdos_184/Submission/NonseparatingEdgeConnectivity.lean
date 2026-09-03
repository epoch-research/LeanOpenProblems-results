import Submission.SeparatingCycleReduction

/-! Nonseparation of every cycle in an even graph implies preservation of
reachability after deleting at most three edges. This supplies a necessary
condition on the unresolved cores, not a decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SeparatingCycleReduction
open Critical EvenCore Rigidity Transversal
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma reachable_delete_cycle_of_no_separation (hs : ¬ HasSeparatingCycle G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) {a b : V}
    (hab : G.Reachable a b) : (G \ p.toSubgraph.spanningCoe).Reachable a b := by
  by_contra hn
  exact hs ⟨u,p,hp,component_count_lt_of_lost_reachability sdiff_le hab hn⟩

lemma even_delete_subsingleton_reachable (he : ∀ v, Even (G.degree v))
    (s : Set (Sym2 V)) (hs : s.Subsingleton) (a b : V) :
    (G.deleteEdges s).Reachable a b ↔ G.Reachable a b := by
  obtain ⟨D,hD,hdec,_⟩ := minimum_cycles he
  exact delete_transversal_reachable D hD hdec s
    (fun H hH e he f hf => hs he.2 hf.2) a b

lemma reachable_delete_piece_of_no_separation (hs : ¬ HasSeparatingCycle G)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    {a b : V} (hab : G.Reachable a b) :
    (G \ H.spanningCoe).Reachable a b := by
  obtain ⟨u⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hH.2)
    u.val u.property
  rw [← hpH]
  exact reachable_delete_cycle_of_no_separation hs hp hab

lemma delete_three_reachable (he : ∀ v, Even (G.degree v))
    (hs : ¬ HasSeparatingCycle G) (s : Finset (Sym2 V)) (hc : s.card ≤ 3)
    (a b : V) : (G.deleteEdges (s : Set (Sym2 V))).Reachable a b ↔ G.Reachable a b := by
  constructor
  · exact SimpleGraph.Reachable.mono (G.deleteEdges_le _)
  · intro hab
    obtain ⟨D,hD,hdec,_⟩ := minimum_cycles he
    by_cases ht : CycleTransversal D (s : Set (Sym2 V))
    · exact (delete_transversal_reachable D hD hdec _ ht a b).mpr hab
    · have hh : ∃ H ∈ D, ¬ (H.edgeSet ∩ (s : Set (Sym2 V))).Subsingleton := by
        by_contra hn
        apply ht
        intro H hH
        by_contra hsub
        exact hn ⟨H,hH,hsub⟩
      obtain ⟨H,hHD,hH⟩ := hh
      have htwo : 2 ≤ (s.filter (fun e => e ∈ H.edgeSet)).card := by
        by_contra hn
        apply hH
        have hsub := Finset.card_le_one.mp (show (s.filter (fun e => e ∈ H.edgeSet)).card ≤ 1 by omega)
        intro e he f hf
        exact hsub e (Finset.mem_filter.mpr ⟨he.2,he.1⟩)
          f (Finset.mem_filter.mpr ⟨hf.2,hf.1⟩)
      let t := s.filter (fun e => e ∉ H.edgeSet)
      have hcard : t.card ≤ 1 := by
        have hh := Finset.card_filter_add_card_filter_not
          (s := s) (p := fun e => e ∈ H.edgeSet)
        change (s.filter (fun e => e ∈ H.edgeSet)).card + t.card = s.card at hh
        omega
      have ht : (t : Set (Sym2 V)).Subsingleton := by
        intro e he f hf
        exact (Finset.card_le_one.mp hcard) e he f hf
      have hHe := regular_two_spanning_even H (hD H hHD).2
      have hRe : ∀ v, Even ((G \ H.spanningCoe).degree v) :=
        sdiff_even he H.spanningCoe_le (by
          simpa only [← SimpleGraph.card_neighborSet_eq_degree,
            ← Nat.card_eq_fintype_card] using hHe)
      have hr := reachable_delete_piece_of_no_separation hs H (hD H hHD) hab
      have hr' := (even_delete_subsingleton_reachable (G := G \ H.spanningCoe) (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hRe) (t : Set (Sym2 V)) ht a b).mpr hr
      apply hr'.mono
      intro x y hxy
      have hm := SimpleGraph.deleteEdges_adj.mp hxy
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hm.1.1,?_⟩
      intro hmem
      apply hm.2
      exact Finset.mem_filter.mpr ⟨hmem,hm.1.2⟩

lemma edge_reachable_four_of_no_separation (he : ∀ v, Even (G.degree v))
    (hs : ¬ HasSeparatingCycle G) {a b : V} (hab : G.Reachable a b) :
    G.IsEdgeReachable 4 a b := by
  intro s hc
  have hcard : s.toFinset.card ≤ 3 := by
    rw [Set.encard_eq_coe_toFinset_card] at hc
    exact Nat.le_of_lt_succ (by exact_mod_cast hc)
  simpa only [Set.coe_toFinset] using (delete_three_reachable he hs s.toFinset hcard a b).mpr hab

lemma edge_connected_four_of_no_separation (he : ∀ v, Even (G.degree v))
    (hs : ¬ HasSeparatingCycle G) (hG : G.Connected) : G.IsEdgeConnected 4 :=
  fun a b => edge_reachable_four_of_no_separation he hs (hG.preconnected a b)

end Erdos184Work.SeparatingCycleReduction
#print axioms Erdos184Work.SeparatingCycleReduction.delete_three_reachable
#print axioms Erdos184Work.SeparatingCycleReduction.edge_connected_four_of_no_separation
