import Submission.CriticalEvenParity
import Submission.OneTailBypass

/-! Universal carrier locking at an inactive degree-two root, and the
one-edge-tail bypass obstruction in arbitrary optimal remainder partitions. -/
namespace Erdos583CriticalRootCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.GroupActivation
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment Erdos583ShortTailCriticalStarDevelopment
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583OneTailBypassDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma degree_two_zero_unique_carrier (T : TrailFamily H p)
    (hp : ∀ j, (T.walk j).IsPath) {r : V}
    (hd : Nat.card (H.neighborSet r)=2) (hq : T.quota r=0) :
    ∃! j, r ∈ (T.walk j).support := by
  have he : Nat.card (H.neighborSet r)+T.quota r=
      2*(Finset.univ.filter fun i ↦ r ∈ (T.walk i).support).card := by
    rw [QuotaParity.degree_sum T r,quota_eq_sum_endpoints T r,←Finset.sum_add_distrib]
    simp_rw [RootCapacity.path_incidence _ (hp _) r]
    rw [←Finset.mul_sum,←Finset.card_filter]
  have hc : (Finset.univ.filter fun i ↦ r ∈ (T.walk i).support).card=1 := by omega
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hc
  have hx (i) : r ∈ (T.walk i).support ↔ i=j := by
    have hh := Finset.ext_iff.mp hj i
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using hh
  exact ⟨j,(hx j).mpr rfl,fun i hi ↦ (hx i).mp hi⟩

lemma degree_two_critical_quota (T : TrailFamily H p)
    (hp : ∀ j, (T.walk j).IsPath) (hn : ∀ j, ¬(T.walk j).Nil) {r x : V}
    (hd : Nat.card (H.neighborSet r)=2) (hq : T.quota r=0)
    (hrx : r ≠ x) (hc : EdgeCritical H p r x) :
    T.quota x ≤ 1 ∧
      (Even (Nat.card (H.neighborSet x)) → T.quota x=0) ∧
      (Odd (Nat.card (H.neighborSet x)) → T.quota x=1) := by
  have hb := critical_individual_quota_bound T hp hn hrx hc
  have hb' : T.quota x ≤ 1 := by omega
  refine ⟨hb',?_,?_⟩
  · intro hx
    obtain ⟨a,ha⟩ := (QuotaParity.quota_even_iff T x).mpr hx
    omega
  · intro hx
    obtain ⟨a,ha⟩ := (QuotaParity.quota_odd_iff T x).mpr hx
    omega

lemma critical_positive_endpoint_locked (T : TrailFamily H p)
    (hp : ∀ j, (T.walk j).IsPath) {r x : V} (hrx : r ≠ x)
    (hc : EdgeCritical H p r x) (j : Fin p)
    (hunique : ∀ i, r ∈ (T.walk i).support → i=j) (hx : 0 < T.quota x) :
    x=T.start j ∨ x=T.finish j := by
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T hx
  have he := hunique i (critical_endpoint_contains T hp hrx (critical_edge_missing T hp hc) hc i hi)
  exact he ▸ hi

omit [Fintype V] in
lemma path_endpoints_edge_no_internal {a b r : V} (P : H.Walk a b) (hp : P.IsPath)
    (hr : r ∈ P.support) (hra : r ≠ a) (hrb : r ≠ b) : s(a,b) ∉ P.edges := by
  intro he
  have hf := CycleEar.path_eq_singleton_of_endpoint_edge P hp (P.adj_of_mem_edges he) he
  rw [hf] at hr
  simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.elim hra hrb

lemma locked_critical_pair_edge_avoids_root (T : TrailFamily H p)
    (hp : ∀ j, (T.walk j).IsPath) {r x y : V}
    (hd : Nat.card (H.neighborSet r)=2) (hq : T.quota r=0)
    (hrx : r ≠ x) (hry : r ≠ y) (hxy : x ≠ y)
    (hcx : EdgeCritical H p r x) (hcy : EdgeCritical H p r y)
    (hx : 0 < T.quota x) (hy : 0 < T.quota y)
    (i : Fin p) (he : s(x,y) ∈ (T.walk i).edges) : r ∉ (T.walk i).support := by
  obtain ⟨j,hjr,hju⟩ := degree_two_zero_unique_carrier T hp hd hq
  have hex := critical_positive_endpoint_locked T hp hrx hcx j hju hx
  have hey := critical_positive_endpoint_locked T hp hry hcy j hju hy
  intro hir
  have hij := hju i hir
  subst i
  have hnot := path_endpoints_edge_no_internal (T.walk j) (hp j) hjr
    (fun hrj ↦ by have hh := DeletionEndpoint.quota_pos_of_endpoint T j (Or.inl hrj); omega)
    (fun hrj ↦ by have hh := DeletionEndpoint.quota_pos_of_endpoint T j (Or.inr hrj); omega)
  rcases hex with hex|hex <;> rcases hey with hey|hey
  · exact hxy (hex.trans hey.symm)
  · apply hnot
    simpa only [hex,hey] using he
  · apply hnot
    simpa only [hex,hey,Sym2.eq_swap (a := T.finish j) (b := T.start j)] using he
  · exact hxy (hex.trans hey.symm)

lemma normal_one_tail_cross_edge_contains_root (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length=1) {s : Fin F.order}
    (h : F.graph.Adj D.root s) (R : F.graph.Walk s D.root)
    (hC : D.rep.cycle=Walk.cons h R)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (i : Fin (normalBudget F D)) (he : s(s,D.rep.finish) ∈ (T.walk i).edges) :
    D.root ∈ (T.walk i).support := by
  obtain ⟨E,hE,hEc,hparts⟩ := CutVertexReduction.path_family_partition_tracked T hp
  have hEq : E.card=normalBudget F D := (normal_partition_lower_bound F D E hE).antisymm' hEc
  obtain ⟨U,hUs,hrest,_,_,hUparts⟩ := replace_path_group_tracked D.family (normalIndices F D)
    (fun j hj ↦ (D.family.one_defect_other_paths D.score D.rep.index D.rep.member_not_path).2
      j (Finset.mem_erase.mp hj).1) E hE hEq
  have hkeep := hrest D.rep.index (by simp [normalIndices])
  let M : RootedCycleRep U D.root :=
    { D.rep with
      start_eq := hkeep.1.trans D.rep.start_eq
      finish_eq := hkeep.2.1.trans D.rep.finish_eq
      subgraph := hkeep.2.2.trans D.rep.subgraph }
  obtain ⟨j,hj,hUj⟩ := hUparts (T.walk i).toSubgraph (hparts i)
  let Q := (T.walk i).mapLe (selectedGraph_le D.family (normalIndices F D))
  have hQe : Q.toSubgraph=(T.walk i).toSubgraph.map
      (Hom.ofLE (selectedGraph_le D.family (normalIndices F D))) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hUQ : (U.walk j).toSubgraph=Q.toSubgraph := hUj.trans hQe.symm
  have heU : s(s,M.finish) ∈ (U.walk j).edges := by
    rw [←Walk.mem_edges_toSubgraph,hUQ,Walk.mem_edges_toSubgraph]
    simpa [Q,Walk.mapLe,M] using he
  have hrU := maximum_one_tail_cross_edge_contains_root U (by rw [hUs]; exact D.score)
    (fun W ↦ by rw [hUs]; exact D.maximum W) D.root M hl h R hC j
    (Finset.mem_erase.mp hj).1.symm heU
  rw [←Walk.mem_verts_toSubgraph,hUQ,Walk.mem_verts_toSubgraph] at hrU
  simpa [Q,Walk.mapLe] using hrU


lemma one_tail_odd_cross_ports_not_adj_remainder (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length=1) (hd : Nat.card (F.graph.neighborSet D.root)=5)
    {s : Fin F.order} (h : F.graph.Adj D.root s) (R : F.graph.Walk s D.root)
    (hC : D.rep.cycle=Walk.cons h R)
    (hs : Odd (Nat.card ((remainder F D).neighborSet s)))
    (ht : Odd (Nat.card ((remainder F D).neighborSet D.rep.finish))) :
    ¬(remainder F D).Adj s D.rep.finish := by
  obtain ⟨T,hT,_⟩ := Erdos583FixedRemainderEnergyDevelopment.normal_remainder_energy_optimum F D
  have hroot := normal_root_degree F D
  have hrdeg : Nat.card ((remainder F D).neighborSet D.root)=2 := by omega
  have hrquota := short_tail_normal_family_quota_zero F D (by omega) T hT
  have hry := (Walk.adj_of_length_eq_one hl).ne
  have hst : s ≠ D.rep.finish := by
    intro he
    apply one_tail_finish_not_cycle F D hl
    rw [hC,←he]
    exact List.mem_cons_of_mem _ R.start_mem_support
  have hcrit_s : EdgeCritical (remainder F D) (normalBudget F D) D.root s := by
    apply root_cycle_edge_critical F D
    rw [hC]
    simpa only [Walk.snd_cons] using (Walk.cons h R).toSubgraph_adj_snd (by simp)
  have hcrit_t := one_tail_ports_critical F D hl D.rep.finish (by simp [ports])
  have hspos : 0 < T.quota s := by
    obtain ⟨a,ha⟩ := (QuotaParity.quota_odd_iff T s).mpr hs
    omega
  have htpos : 0 < T.quota D.rep.finish := by
    obtain ⟨a,ha⟩ := (QuotaParity.quota_odd_iff T D.rep.finish).mpr ht
    omega
  intro hadj
  obtain ⟨j,hj⟩ := (T.cover s(s,D.rep.finish)).mp hadj
  have he := (T.walk j).mem_edges_toSubgraph.mp hj
  exact locked_critical_pair_edge_avoids_root T hT hrdeg hrquota h.ne hry hst
    hcrit_s hcrit_t hspos htpos j he
    (normal_one_tail_cross_edge_contains_root F D hl h R hC T hT j he)

lemma one_tail_odd_cross_ports_not_adj (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hl : D.rep.tail.length=1) (hd : Nat.card (F.graph.neighborSet D.root)=5)
    {s : Fin F.order} (h : F.graph.Adj D.root s) (R : F.graph.Walk s D.root)
    (hC : D.rep.cycle=Walk.cons h R)
    (hs : Odd (Nat.card ((remainder F D).neighborSet s)))
    (ht : Odd (Nat.card ((remainder F D).neighborSet D.rep.finish))) :
    ¬F.graph.Adj s D.rep.finish := by
  have hnot := one_tail_odd_cross_ports_not_adj_remainder F D hl hd h R hC hs ht
  intro hadj
  apply hnot
  change (selectedGraph D.family (Finset.univ.erase D.rep.index)).Adj s D.rep.finish
  rw [CubicRemainder.selected_erase_eq_delete,deleteEdges_adj]
  refine ⟨hadj,?_⟩
  rw [D.rep.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
  intro he
  rcases he with he|he
  · exact one_tail_finish_not_cycle F D hl (Walk.mem_support_of_adj_toSubgraph he.symm)
  · obtain ⟨g,hS⟩ := ShortLollipop.one_edge_form D.rep.tail hl
    rw [hS,Walk.mem_edges_toSubgraph] at he
    simp only [Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false,
      Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk] at he
    rcases he with ⟨h1,_⟩|⟨h1,h2⟩
    · exact h.ne h1.symm
    · exact g.ne h2.symm

end Erdos583CriticalRootCarrierDevelopment
