import Submission.OutsideModelSelection
import Submission.CycleExactLabeling
import Submission.SupportedBlockLabeling

/-! Every nonempty count-critical graph of count at most three has a degree-two
vertex. This is a restricted critical-structure theorem, not a uniform bound
on arbitrary critical counts and not a settlement of Spec. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CountThreeDegreeTwo
open CountCritical CycleNumberSubmodularity HighGirthCritical EvenCycleCore
open CountThreeAttachmentData AttachmentModelFacts AttachmentModelCompatibility
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 1000000

lemma exact_labels_card (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (hind : C.IsInduced)
    {l : ℕ} (hlen : C.verts.ncard = l) (hl : 3 ≤ l) :
    ∃ e : Fin l ≃ C.verts, ∀ u v,
      G.Adj (e u).val (e v).val ↔ (cycleGraph l).Adj u v := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hl
  have heq : l = n+3 := by omega
  rw [heq] at hlen ⊢
  exact CycleExactLabeling.exists_exact_labels C hc hind hlen

lemma decomposition_of_small_cycle
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (hlen : C.verts.ncard = 3 ∨ C.verts.ncard = 4)
    (htri : C.verts.ncard = 4 → ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    (hout : NoTwoCycles (avoid G C.verts)) :
    ∃ D : Finset G.Subgraph,
      (∀ P ∈ D, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  have hCS := CriticalOutsideCycles.cycle_verts_in_support C hc.2
  have hmodel : ∃ i : Fin 12, (model i).girth = C.verts.ncard ∧
      ∃ e : Fin (model i).outsideOrder ≃ ↥(G.support \ C.verts), ∀ a b,
        G.Adj (e a).val (e b).val ↔
          s(outsideVertex (model i) a.val,outsideVertex (model i) b.val) ∈ (model i).base := by
    rcases hlen with hlen | hlen
    · obtain ⟨i,hi,e,he⟩ := OutsideModelSelection.triangle_model hfour C hc hind hlen hout
      exact ⟨i,hi.trans hlen.symm,e,he⟩
    · obtain ⟨i,hi,e,he⟩ := OutsideModelSelection.quadrilateral_model hfour (htri hlen) C hc hind hlen hout
      exact ⟨i,hi.trans hlen.symm,e,he⟩
  obtain ⟨i,hi,eo,heo⟩ := hmodel
  obtain ⟨ec,hec⟩ := exact_labels_card C hc hind hi.symm (model_bounds i).1
  apply SupportedBlockLabeling.decomposition_from_labels i C hCS ec eo
  · intro a b
    exact (hec a b).trans (base_cycle i a b)
  · exact heo
  · exact hfour
  · intro hquad
    exact htri (hi.symm.trans hquad)

lemma exists_degree_two_of_count_le_three {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3) (hne : G ≠ ⊥) :
    ∃ v, G.degree v = 2 := by
  by_contra! hno
  have hfour := LowCountCritical.supported_degree_eq_four_of_count_le_three hG hk hne hno
  obtain ⟨a,p,hp,hg⟩ := exists_shortest_cycle G hne (by
    intro v hv
    rw [hfour v hv]
    omega)
  have hlen : p.length ≤ 4 := by
    by_contra! hn
    obtain ⟨v,hv⟩ := degree_two_of_count_le_three_high_girth hG hk hne (by
      intro v q hq
      have hh := G.girth_le_length hq
      rw [hg] at hh
      omega)
    exact hno v hv
  have hc := cycle_subgraph_regular G hp
  have hcard := trail_spanning_edge_card p hp.isTrail
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hcard
  change p.toSubgraph.edgeSet.ncard = p.length at hcard
  rw [regular_two_edge_vertex_card p.toSubgraph hc.2] at hcard
  have hsmall : p.toSubgraph.verts.ncard = 3 ∨ p.toSubgraph.verts.ncard = 4 := by
    have hh := hp.three_le_length
    omega
  have ht : p.toSubgraph.verts.ncard = 4 →
      ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False := by
    intro hquad u v w huv hvw hwu
    obtain ⟨q,hq,hql⟩ := NoTwoCyclesEdges.triangle_walk huv hvw hwu
    have hh := G.girth_le_length hq
    rw [hg,hql] at hh
    omega
  have hout : NoTwoCycles (avoid G p.toSubgraph.verts) :=
    CriticalOutsideCycles.outside_cycles_not_disjoint hG hk hno p.toSubgraph hc
  obtain ⟨D,hD,hd,hb⟩ := decomposition_of_small_cycle hfour p.toSubgraph hc
    (ShortestCycle.isInduced p hp hg) hsmall ht hout
  have hnum := number_le G D hD hd
  rw [hG.2.1] at hnum
  obtain ⟨v,hv⟩ := LowCountCritical.exists_degree_two_of_count_le_two hG (by omega) hne
  exact hno v hv

end Erdos184.CountThreeDegreeTwo
