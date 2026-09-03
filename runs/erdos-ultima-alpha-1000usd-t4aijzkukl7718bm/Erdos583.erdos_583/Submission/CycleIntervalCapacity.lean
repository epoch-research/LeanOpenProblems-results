import Submission.CollisionEndpointLabels

/-! Endpoint collisions in near-complete cycle remainders under a bound on
vertex incidence among the core intervals. -/
namespace Erdos583CycleIntervalCapacityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CollisionEndpointLabelsDevelopment
open Erdos583CompletePrescribedPairsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma path_family_incidence {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) (w : V) :
    Nat.card (G.neighborSet w)+T.quota w =
      2*(Finset.univ.filter fun i ↦ w ∈ (T.walk i).support).card := by
  classical
  rw [QuotaParity.degree_sum T w,quota_eq_sum_endpoints T w,←Finset.sum_add_distrib]
  simp_rw [RootCapacity.path_incidence _ (hp _)]
  rw [←Finset.mul_sum,←Finset.card_filter]

lemma near_complete_other_neighbor_card {V : Type*} [Fintype V] {u v : V}
    (w : V) (hwu : w ≠ u) (hwv : w ≠ v) :
    Nat.card (((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).neighborSet w)=
      Fintype.card V-1 := by
  have hN : ((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).neighborSet w=
      (⊤ : SimpleGraph V).neighborSet w := by
    ext z
    simp only [mem_neighborSet,deleteEdges_adj,top_adj,Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro hwz
      refine ⟨hwz,?_⟩
      intro hh
      exact (Sym2.eq_iff.mp hh).elim (fun h ↦ hwu h.1) (fun h ↦ hwv h.1)
  rw [hN,Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  exact complete_graph_degree w

lemma near_complete_ordinary_quota_one {V : Type*} [Fintype V] {H : SimpleGraph V}
    {t : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) (t+1))
    (hp : ∀ i, (T.walk i).IsPath)
    (u v : V) (hcard : 2*t+2=Fintype.card V)
    (hH : H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)})
    (w : V) (hwu : w ≠ u) (hwv : w ≠ v)
    (hcap : (Finset.univ.filter fun i ↦ w ∈ (T.walk i).support).card ≤ t) :
    T.quota w=1 := by
  classical
  have hdeg : Nat.card (H.neighborSet w)=Fintype.card V-1 := by
    rw [hH]; exact near_complete_other_neighbor_card w hwu hwv
  have hdel := ncard_neighbor_delete_subgraph_add C.toSubgraph w
  have hinc := path_family_incidence T hp w
  have hcy : (C.toSubgraph.neighborSet w).ncard ≤ 2 := by
    by_cases hw : w ∈ C.support
    · exact (hC.ncard_neighborSet_toSubgraph_eq_two hw).le
    · have hn : C.toSubgraph.neighborSet w=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hw (Walk.mem_support_of_adj_toSubgraph hx)
      simp [hn]
  have ho : Odd (Nat.card (H.neighborSet w)) := by
    rw [hdeg,←hcard]
    exact ⟨t,by omega⟩
  have hor : Odd (Nat.card ((H.deleteEdges C.toSubgraph.edgeSet).neighborSet w)) := by
    rw [Nat.card_coe_set_eq,Nat.odd_iff] at ho ⊢
    exact (delete_cycle_preserves_degree_parity hC w).trans ho
  have hq := ((QuotaParity.quota_odd_iff T w).mpr hor).pos
  simp only [Nat.card_coe_set_eq] at hdeg hinc
  omega

lemma near_complete_special_quota_even {V : Type*} [Fintype V] {H : SimpleGraph V}
    {t k : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) k)
    (u v : V) (huv : u ≠ v) (hcard : 2*t+2=Fintype.card V)
    (hH : H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)}) :
    Even (T.quota u) := by
  classical
  apply (QuotaParity.quota_even_iff T u).mpr
  have hdel := DegreeThreeReduction.delete_edge_neighbor_add_one
    (show (⊤ : SimpleGraph V).Adj u v from huv)
  have hdeg : Nat.card ((⊤ : SimpleGraph V).neighborSet u)=Fintype.card V-1 := by
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    exact complete_graph_degree u
  have hdu : Nat.card (H.neighborSet u)=2*t := by
    rw [hH]
    omega
  have he : Even (Nat.card (H.neighborSet u)) := by rw [hdu]; exact even_two_mul t
  rw [Nat.card_coe_set_eq,Nat.even_iff] at he ⊢
  exact (delete_cycle_preserves_degree_parity hC u).trans he

lemma near_complete_interval_collision {V : Type*} [Fintype V] {H : SimpleGraph V}
    {t : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) (t+1))
    (hp : ∀ i, (T.walk i).IsPath)
    (u v : V) (huv : u ≠ v) (hcard : 2*t+2=Fintype.card V)
    (hH : H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)})
    (hcap : ∀ w, w ≠ u → w ≠ v →
      (Finset.univ.filter fun i ↦ w ∈ (T.walk i).support).card ≤ t) :
    ∃ w d, ((w=u ∧ d=v) ∨ (w=v ∧ d=u)) ∧
      (∀ z, T.endpoint z ≠ w) ∧ ∃ i j, i ≠ j ∧ T.endpoint i=d ∧ T.endpoint j=d ∧
      Function.Bijective (fun z ↦ if z=i then w else T.endpoint z) := by
  exact trail_endpoint_collision T u v huv (by omega)
    (fun w hwu hwv ↦ near_complete_ordinary_quota_one C hC T hp u v hcard hH w hwu hwv
      (hcap w hwu hwv))
    (near_complete_special_quota_even C hC T u v huv hcard hH)

end Erdos583CycleIntervalCapacityDevelopment
