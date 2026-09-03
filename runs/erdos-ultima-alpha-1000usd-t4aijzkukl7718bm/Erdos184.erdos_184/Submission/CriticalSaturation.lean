import Submission.TightDual

/-! A saturated vertex of a cycle-critical even graph is a feedback vertex.
This does not require minimality among all even subgraphs. It supplies no
uniform bound for the unsaturated case. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CriticalSaturation
open Critical EvenCore Rigidity CycleCertificates
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma cycle_hits_saturated (hc : CycleCritical G) (v : V)
    (hs : G.degree v = 2 * number G) :
    ∀ u (p : G.Walk u u), p.IsCycle → v ∈ p.support := by
  intro u p hp
  by_contra hv
  have hv' : v ∉ p.toSubgraph.verts := fun h => hv (p.mem_verts_toSubgraph.mp h)
  have hz := regular_two_spanning_degree p.toSubgraph (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using (cycle_coe_regular G hp).2) v
  rw [if_neg hv'] at hz
  have hd := degree_sdiff_add G p.toSubgraph.spanningCoe p.toSubgraph.spanningCoe_le v
  have hb := StarCore.number_degree_bound (G \ p.toSubgraph.spanningCoe) v
  have hn := hc u p hp
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hz hd hb hs
  omega

lemma saturated_iff_feedback (he : ∀ w, Even (G.degree w))
    (hc : CycleCritical G) (v : V) :
    G.degree v = 2 * number G ↔ (G.induce {v}ᶜ).IsAcyclic := by
  constructor
  · intro hs
    exact (StarCore.cycle_hits_iff_induce_acyclic v).mp (cycle_hits_saturated hc v hs)
  · intro ha
    exact (StarCore.twice_number_eq_degree_of_cycle_hits he v
      ((StarCore.cycle_hits_iff_induce_acyclic v).mpr ha)).symm

lemma saturated_rigid_and_sparse (he : ∀ w, Even (G.degree w))
    (hc : CycleCritical G) (v : V) (hs : G.degree v = 2 * number G) :
    CycleRigid G ∧ G.edgeFinset.card ≤ 2 * Fintype.card V ∧
      2 * number G < Fintype.card V := by
  have hh := cycle_hits_saturated hc v hs
  have hw := feedbackWeight_certificate v hh
  refine ⟨rigid_of_cycle_hits he v hh,
    CertificateStructure.UnitCycleWeight.edge_bound hw, ?_⟩
  rw [← hs]
  exact G.degree_lt_card_verts v

lemma degree_gap_of_nonrigid (he : ∀ w, Even (G.degree w))
    (hc : CycleCritical G) (hr : ¬ CycleRigid G) (v : V) :
    G.degree v + 2 ≤ 2 * number G := by
  have hb := StarCore.number_degree_bound G v
  have hs : G.degree v ≠ 2 * number G := by
    intro h
    exact hr (saturated_rigid_and_sparse he hc v h).1
  have hv := Nat.even_iff.mp (he v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb hs hv ⊢
  omega

#print axioms cycle_hits_saturated
#print axioms saturated_iff_feedback
#print axioms saturated_rigid_and_sparse
#print axioms degree_gap_of_nonrigid
end Erdos184Work.CriticalSaturation
