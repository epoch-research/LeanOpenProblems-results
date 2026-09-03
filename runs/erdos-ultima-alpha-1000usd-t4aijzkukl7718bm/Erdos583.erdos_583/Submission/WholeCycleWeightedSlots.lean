import Submission.WeightedCycleEndpoints
import Submission.DeleteMemberFamily

/-! Weighted endpoint-slot bounds for a whole cycle in an arbitrary indexed
trail family, including the stronger bound at a strict vertex budget. -/
namespace Erdos583WholeCycleWeightedSlotsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails
open Erdos583WeightedCycleEndpointsDevelopment Erdos583DeleteMemberFamilyDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma whole_cycle_weighted_common_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (S : Finset V)
    (hSC : ∀ v ∈ S, v ∈ C.support)
    (hv : ∀ v ∈ S, ∀ j, j ≠ i → v ∈ (T.walk j).support) :
    2*k*S.card ≤ (∑ v ∈ S, Nat.card (G.neighborSet v))+2*(k-1) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ t =>
    obtain ⟨U,_,_,hUs,_⟩ := exists_delete_member_family T i C.toSubgraph.edgeSet
      (congrArg Subgraph.edgeSet hi)
    have hall (v : V) (hvS : v ∈ S) (j : Fin t) : v ∈ (U.walk j).support := by
      rw [hUs]
      exact hv v hvS _ (i.succAbove_ne j)
    have hh := weighted_common_cycle_bound C hC U S hSC hall
    simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.mul_add,Nat.mul_one] using hh

lemma whole_cycle_common_bound_of_degree {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (S : Finset V)
    (hSC : ∀ v ∈ S, v ∈ C.support)
    (hv : ∀ v ∈ S, ∀ j, j ≠ i → v ∈ (T.walk j).support)
    (d : ℕ) (hdeg : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤ d) :
    (2*k-d)*S.card ≤ 2*(k-1) := by
  have hb := whole_cycle_weighted_common_bound T i C hC hi S hSC hv
  have hs := Finset.sum_le_sum (s := S) hdeg
  simp only [Finset.sum_const,smul_eq_mul] at hs
  by_cases hd : d ≤ 2*k
  · have he := Nat.sub_add_cancel hd
    nlinarith
  · have he : 2*k-d=0 := by omega
    simp [he]

lemma whole_cycle_common_card_strict_budget {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (S : Finset V)
    (hSC : ∀ v ∈ S, v ∈ C.support)
    (hv : ∀ v ∈ S, ∀ j, j ≠ i → v ∈ (T.walk j).support)
    (hbudget : Fintype.card V+1 ≤ 2*k) : S.card+1 ≤ k := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ t =>
    obtain ⟨U,_,_,hUs,_⟩ := exists_delete_member_family T i C.toSubgraph.edgeSet
      (congrArg Subgraph.edgeSet hi)
    have hall (v : V) (hvS : v ∈ S) (j : Fin t) : v ∈ (U.walk j).support := by
      rw [hUs]
      exact hv v hvS _ (i.succAbove_ne j)
    have hh := common_cycle_card_of_strict_budget C hC U S hSC hall (by omega)
    omega

lemma whole_cycle_all_common_length_strict_budget {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (i : Fin k) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hv : ∀ v ∈ C.support, ∀ j, j ≠ i → v ∈ (T.walk j).support)
    (hbudget : Fintype.card V+1 ≤ 2*k) : C.length+1 ≤ k := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ t =>
    obtain ⟨U,_,_,hUs,_⟩ := exists_delete_member_family T i C.toSubgraph.edgeSet
      (congrArg Subgraph.edgeSet hi)
    have hall (v : V) (hvC : v ∈ C.support) (j : Fin t) : v ∈ (U.walk j).support := by
      rw [hUs]
      exact hv v hvC _ (i.succAbove_ne j)
    have hh := all_common_cycle_length_of_strict_budget C hC U hall (by omega)
    omega

end Erdos583WholeCycleWeightedSlotsDevelopment
