import Submission.Work

/-! Degree-sensitive endpoint charging on vertices shared by a cycle and
all members of its remainder. No maximality or path-normality is assumed. -/
namespace Erdos583WeightedCycleEndpointsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma common_trail_degree_quota_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ}
    (T : TrailFamily G t) (v : V) (hv : ∀ i, v ∈ (T.walk i).support) :
    2*t ≤ Nat.card (G.neighborSet v)+T.quota v := by
  classical
  have hterm (i : Fin t) : 2 ≤ ((T.walk i).toSubgraph.neighborSet v).ncard+
      ((if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0)) := by
    rw [RootCapacity.trail_incidence (T.walk i) (T.isTrail i) v]
    have hc : 0 < (T.walk i).support.count v := List.count_pos_iff.mpr (hv i)
    omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hterm i)
  rw [Finset.sum_add_distrib,←QuotaParity.degree_sum T v,←quota_eq_sum_endpoints T v] at hh
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm] using hh

lemma common_cycle_degree_quota_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (G.deleteEdges C.toSubgraph.edgeSet) t)
    (v : V) (hvC : v ∈ C.support) (hv : ∀ i, v ∈ (T.walk i).support) :
    2*t+2 ≤ Nat.card (G.neighborSet v)+T.quota v := by
  have hb := common_trail_degree_quota_bound T v hv
  have he := ncard_neighbor_delete_subgraph_add C.toSubgraph v
  rw [hC.ncard_neighborSet_toSubgraph_eq_two hvC] at he
  simp only [Nat.card_coe_set_eq] at hb ⊢
  omega

lemma quota_sum_on_finset_le {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ}
    (T : TrailFamily G t) (S : Finset V) : ∑ v ∈ S, T.quota v ≤ 2*t := by
  rw [←RootEnergy.sum_quota T]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)

lemma weighted_common_cycle_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (G.deleteEdges C.toSubgraph.edgeSet) t) (S : Finset V)
    (hSC : ∀ v ∈ S, v ∈ C.support) (hv : ∀ v ∈ S, ∀ i, v ∈ (T.walk i).support) :
    (2*t+2)*S.card ≤ (∑ v ∈ S, Nat.card (G.neighborSet v))+2*t := by
  have hh := Finset.sum_le_sum (s := S) (fun v hvS ↦
    common_cycle_degree_quota_bound C hC T v (hSC v hvS) (hv v hvS))
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hh
  have hq := quota_sum_on_finset_le T S
  nlinarith

lemma common_cycle_bound_of_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (G.deleteEdges C.toSubgraph.edgeSet) t) (S : Finset V)
    (hSC : ∀ v ∈ S, v ∈ C.support) (hv : ∀ v ∈ S, ∀ i, v ∈ (T.walk i).support)
    (d : ℕ) (hdeg : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤ d) :
    (2*t+2-d)*S.card ≤ 2*t := by
  have hb := weighted_common_cycle_bound C hC T S hSC hv
  have hs := Finset.sum_le_sum (s := S) hdeg
  simp only [Finset.sum_const,smul_eq_mul] at hs
  by_cases hd : d ≤ 2*t+2
  · have he := Nat.sub_add_cancel hd
    nlinarith
  · have he : 2*t+2-d=0 := by omega
    simp [he]

lemma common_cycle_card_of_strict_budget {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (G.deleteEdges C.toSubgraph.edgeSet) t) (S : Finset V)
    (hSC : ∀ v ∈ S, v ∈ C.support) (hv : ∀ v ∈ S, ∀ i, v ∈ (T.walk i).support)
    (hbudget : Fintype.card V+1 ≤ 2*t+2) : S.card ≤ t := by
  classical
  have hdeg (v : V) (_ : v ∈ S) : Nat.card (G.neighborSet v) ≤ 2*t := by
    have hl : Nat.card (G.neighborSet v) < Fintype.card V := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using G.degree_lt_card_verts v
    omega
  have hh := common_cycle_bound_of_degree C hC T S hSC hv (2*t) hdeg
  have he : 2*t+2-2*t=2 := by omega
  rw [he] at hh
  omega

lemma all_common_cycle_length_of_strict_budget {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (G.deleteEdges C.toSubgraph.edgeSet) t)
    (hv : ∀ v ∈ C.support, ∀ i, v ∈ (T.walk i).support)
    (hbudget : Fintype.card V+1 ≤ 2*t+2) : C.length ≤ t := by
  classical
  have hh := common_cycle_card_of_strict_budget C hC T C.support.toFinset
    (fun v hv ↦ List.mem_toFinset.mp hv) (fun v hvS ↦ hv v (List.mem_toFinset.mp hvS)) hbudget
  have hc : C.support.toFinset.card=C.length := by
    rw [←Set.ncard_coe_finset]
    convert cycle_support_ncard hC using 1
    congr 1
    ext v
    simp
  omega

end Erdos583WeightedCycleEndpointsDevelopment
