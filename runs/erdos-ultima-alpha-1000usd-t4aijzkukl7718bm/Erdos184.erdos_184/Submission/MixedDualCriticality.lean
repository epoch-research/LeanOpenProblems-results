import Submission.TightDual

/-! A full cycle-and-single-edge dual is exact on an edge-critical graph only
when the graph is acyclic. This concerns the full mixed dual, not a dual on an
optimal even remainder, and does not settle the original conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MixedDualCriticality
open Critical Weighted CycleCertificates TightDual
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Signed weights feasible for both singleton and cycle pieces. -/
def MixedUpperWeight (G : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  (∀ e ∈ G.edgeSet, w e ≤ 1) ∧ CycleUpperWeight G w

lemma MixedUpperWeight.mono {w : Sym2 V → ℝ} (hw : MixedUpperWeight G w)
    {R : SimpleGraph V} (hRG : R ≤ G) : MixedUpperWeight R w :=
  ⟨fun e he => hw.1 e (SimpleGraph.edgeSet_mono hRG he), hw.2.mono hRG⟩

lemma mixed_piece_weight_le {w : Sym2 V → ℝ} (hw : MixedUpperWeight G w)
    (H : G.Subgraph) (hH : IsCycleOrEdge H.coe) :
    (∑ e ∈ H.spanningCoe.edgeFinset, w e) ≤ 1 := by
  rcases hH with hcy | hed
  · apply piece_weight_le hw.2 H
    simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hcy
  · have hc : H.spanningCoe.edgeFinset.card = 1 := (subgraph_edge_card H).trans hed
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc
    rw [he, Finset.sum_singleton]
    apply hw.1
    apply SimpleGraph.edgeSet_mono H.spanningCoe_le
    apply SimpleGraph.mem_edgeFinset.mp
    rw [he]
    exact Finset.mem_singleton_self e

lemma MixedUpperWeight.total_le_number {w : Sym2 V → ℝ}
    (hw : MixedUpperWeight G w) :
    (∑ e ∈ G.edgeFinset, w e) ≤ (number G : ℝ) := by
  obtain ⟨D, hD, hd, hc⟩ := exists_minimum G
  rw [decomposition_weight_eq D hd w]
  calc
    _ ≤ ∑ _H ∈ D, (1 : ℝ) :=
      Finset.sum_le_sum (fun H hH => mixed_piece_weight_le hw H (hD H hH))
    _ = _ := by simp [hc]

/-- Edge exposure gives a lower bound on every individual edge weight in
terms of the integral-minus-dual gap. -/
lemma edge_weight_lower {w : Sym2 V → ℝ} (hw : MixedUpperWeight G w)
    (hc : EdgeCritical G) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ f ∈ G.edgeFinset, w f) - (number G : ℝ) + 1 ≤ w e := by
  have hb := (hw.mono (G.deleteEdges_le {e})).total_le_number
  have hdel : (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_diff, Set.mem_singleton_iff, Finset.mem_erase]
    tauto
  have hs := Finset.sum_erase_add (s := G.edgeFinset) (f := w)
    (SimpleGraph.mem_edgeFinset.mpr he)
  simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at hb hdel hs ⊢
  rw [hdel] at hb
  have hn : (number G : ℝ) = (number (G.deleteEdges {e}) : ℝ) + 1 := by
    exact_mod_cast hc ⟨e, he⟩
  linarith

lemma cycle_gap_bound {w : Sym2 V → ℝ} (hw : MixedUpperWeight G w)
    (hc : EdgeCritical G) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    (p.length : ℝ) - 1 ≤
      (p.length : ℝ) * ((number G : ℝ) - ∑ e ∈ G.edgeFinset, w e) := by
  have hs : (p.length : ℝ) *
      ((∑ e ∈ G.edgeFinset, w e) - (number G : ℝ) + 1) ≤ walkWeight w p := by
    calc
      _ = ∑ _e ∈ p.toSubgraph.spanningCoe.edgeFinset,
          ((∑ e ∈ G.edgeFinset, w e) - (number G : ℝ) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, cycle_edge_count G hp]
      _ ≤ ∑ e ∈ p.toSubgraph.spanningCoe.edgeFinset, w e := by
        apply Finset.sum_le_sum
        intro e he
        exact edge_weight_lower hw hc e
          (SimpleGraph.edgeSet_mono p.toSubgraph.spanningCoe_le
            (SimpleGraph.mem_edgeFinset.mp he))
      _ = _ := cycle_edge_weight p hp w
  have hu := hw.2 u p hp
  nlinarith

/-- In particular, every cyclic edge-critical graph has a mixed-dual gap of
at least two thirds. This is not a bound on the integral decomposition number. -/
lemma cyclic_gap {w : Sym2 V → ℝ} (hw : MixedUpperWeight G w)
    (hc : EdgeCritical G) (hcy : ¬ G.IsAcyclic) :
    (2 : ℝ) / 3 ≤ (number G : ℝ) - ∑ e ∈ G.edgeFinset, w e := by
  obtain ⟨u, p, hp⟩ : ∃ u, ∃ p : G.Walk u u, p.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hcy
  have hb := cycle_gap_bound hw hc p hp
  have hlen : (3 : ℝ) ≤ p.length := by exact_mod_cast hp.three_le_length
  by_contra h
  have hgap : (number G : ℝ) - ∑ e ∈ G.edgeFinset, w e < (2 : ℝ) / 3 :=
    lt_of_not_ge h
  have hmul := mul_le_mul_of_nonneg_right hlen
    (show 0 ≤ 1 - ((number G : ℝ) - ∑ e ∈ G.edgeFinset, w e) by linarith)
  nlinarith

lemma exact_mixed_dual_iff_acyclic (hc : EdgeCritical G) :
    (∃ w : Sym2 V → ℝ, MixedUpperWeight G w ∧
      (number G : ℝ) ≤ ∑ e ∈ G.edgeFinset, w e) ↔ G.IsAcyclic := by
  constructor
  · rintro ⟨w, hw, he⟩
    by_contra hcy
    have hgap := cyclic_gap hw hc hcy
    linarith
  · intro ha
    refine ⟨fun _ => 1, ⟨fun _ _ => le_rfl, ?_⟩, ?_⟩
    · intro u p hp
      exact (ha p hp).elim
    · simpa using (show (number G : ℝ) ≤ (G.edgeFinset.card : ℝ) by
        exact_mod_cast number_le_edges G)

end Erdos184Work.MixedDualCriticality
#print axioms Erdos184Work.MixedDualCriticality.edge_weight_lower
#print axioms Erdos184Work.MixedDualCriticality.cyclic_gap
#print axioms Erdos184Work.MixedDualCriticality.exact_mixed_dual_iff_acyclic
