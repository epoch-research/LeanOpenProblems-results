import Submission.OneFanCycleAbsorption
import Submission.CleanCycleMaximality

/-! Every unused cycle has an internal contact with a packed path whose own
endpoint lies on that cycle. This does not eliminate arbitrary contacts. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Maximal.endpoint_path_meets_unused_cycle_again {L : List (Piece G)} (hL : Maximal L)
    {a v : V} (C : G.Walk a a) (hC : C.IsCycle) (hv : v ∈ C.support)
    (hunused : (edgeList L).Disjoint C.edges)
    {p : Piece G} (hp : p ∈ L) (hpv : v = p.src ∨ v = p.dst) :
    ∃ w, w ∈ p.walk.support ∧ w ∈ C.support ∧ w ≠ v := by
  by_contra! hn
  have hcard := hC.ncard_neighborSet_toSubgraph_eq_two hv
  obtain ⟨x,hx⟩ := (Set.ncard_pos (s := C.toSubgraph.neighborSet v)).mp
    (show 0 < (C.toSubgraph.neighborSet v).ncard by omega)
  have hvx := C.toSubgraph.adj_sub hx
  have hex : s(v,x) ∈ C.edges := C.mem_edges_toSubgraph.mp hx
  obtain ⟨Q,hQ,hperm⟩ := CertificateStructure.cycle_edge_cons C hC hvx hex
  have hQS : Q.support ⊆ C.support := by
    intro w hw
    obtain ⟨e,he,hwe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil
      (Q.not_nil_of_ne hvx.ne.symm)).mp hw
    exact Walk.mem_support_of_mem_edges (hperm.mem_iff.mp (List.mem_cons_of_mem _ he)) hwe
  refine FanAbsorption.no_clean_endpoint hL Q hvx hQ ?_ p hp hpv ?_
  · intro e he hce
    exact hunused he (hperm.mem_iff.mp hce)
  · intro w hwp hwq
    exact hn w hwp (hQS hwq)

lemma Maximal.clean_endpoint_path_both_ends_on_cycle {L : List (Piece G)} (hL : Maximal L)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hunused : (edgeList L).Disjoint C.edges)
    {p : Piece G} (hp : p ∈ L)
    (hend : p.src ∈ C.support ∨ p.dst ∈ C.support)
    (hclean : ∀ w, w ∈ p.walk.support → w ∈ C.support → w = p.src ∨ w = p.dst) :
    p.src ∈ C.support ∧ p.dst ∈ C.support := by
  rcases hend with hend | hend
  · obtain ⟨w,hwp,hwC,hw⟩ := hL.endpoint_path_meets_unused_cycle_again C hC hend hunused hp (Or.inl rfl)
    have he := (hclean w hwp hwC).resolve_left hw
    exact ⟨hend,he ▸ hwC⟩
  · obtain ⟨w,hwp,hwC,hw⟩ := hL.endpoint_path_meets_unused_cycle_again C hC hend hunused hp (Or.inr rfl)
    have he := (hclean w hwp hwC).resolve_right hw
    exact ⟨he ▸ hwC,hend⟩

lemma Maximal.unused_cycle_endpoint_owned_internal_contact {L : List (Piece G)}
    (hL : Maximal L) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hunused : (edgeList L).Disjoint C.edges) :
    ∃ p ∈ L, (p.src ∈ C.support ∨ p.dst ∈ C.support) ∧
      ∃ w ∈ p.walk.support, w ∈ C.support ∧ w ≠ p.src ∧ w ≠ p.dst := by
  by_contra hn
  have hclean : ∀ p ∈ L, (p.src ∈ C.support ∨ p.dst ∈ C.support) →
      ∀ w, w ∈ p.walk.support → w ∈ C.support → w = p.src ∨ w = p.dst := by
    intro p hp hend w hwp hwC
    by_contra hw
    exact hn ⟨p,hp,hend,w,hwp,hwC,fun h => hw (Or.inl h),fun h => hw (Or.inr h)⟩
  obtain ⟨p,hp,hpa⟩ := List.mem_flatMap.mp (hL.1.2.2 a)
  have hpa : a = p.src ∨ a = p.dst := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hpa
  have hpC : p.src ∈ C.support ∨ p.dst ∈ C.support := by
    rcases hpa with h | h
    · exact Or.inl (h ▸ C.start_mem_support)
    · exact Or.inr (h ▸ C.start_mem_support)
  have hpend := hL.clean_endpoint_path_both_ends_on_cycle C hC hunused hp hpC (hclean p hp hpC)
  have hcard := hC.ncard_neighborSet_toSubgraph_eq_two hpend.1
  have hx : ∃ x, C.toSubgraph.Adj p.src x ∧ x ≠ p.dst := by
    by_contra! hh
    have hsub : C.toSubgraph.neighborSet p.src ⊆ {p.dst} := fun x hx => hh x hx
    have hh := Set.ncard_le_ncard hsub
    rw [hcard,Set.ncard_singleton] at hh
    omega
  obtain ⟨x,hx,hxd⟩ := hx
  have hxs : x ≠ p.src := (C.toSubgraph.adj_sub hx).ne.symm
  have hxC : x ∈ C.support := C.snd_mem_support_of_mem_edges (C.mem_edges_toSubgraph.mp hx)
  obtain ⟨q,hq,hqx⟩ := List.mem_flatMap.mp (hL.1.2.2 x)
  have hqx : x = q.src ∨ x = q.dst := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hqx
  have hqC : q.src ∈ C.support ∨ q.dst ∈ C.support := by
    rcases hqx with h | h
    · exact Or.inl (h ▸ hxC)
    · exact Or.inr (h ▸ hxC)
  have hqend := hL.clean_endpoint_path_both_ends_on_cycle C hC hunused hq hqC (hclean q hq hqC)
  have hqp : q ≠ p := by
    intro h
    subst q
    exact hqx.elim hxs hxd
  obtain ⟨N,hN⟩ := two_at_front hp hq hqp
  have hLN := hL.perm hN
  obtain ⟨r,s,hr,hs⟩ := Absorption.absorb_clean_cycle_ended p q C hC
    hpend.1 hpend.2 hqend.1 hqend.2 hLN.1.first_two_endpoints_distinct
    (hclean p hp hpC) (hclean q hq hqC)
  apply hLN.no_two_exchange hC.isTrail.edges_nodup _ _ hr hs
  · simpa only [Walk.length_edges] using hC.three_le_length.trans_lt' (by omega)
  · intro e he hce
    exact hunused ((edgeList_perm hN).mem_iff.mpr he) hce

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Maximal.endpoint_path_meets_unused_cycle_again
#print axioms Erdos184Work.OddPaths.Maximal.unused_cycle_endpoint_owned_internal_contact
