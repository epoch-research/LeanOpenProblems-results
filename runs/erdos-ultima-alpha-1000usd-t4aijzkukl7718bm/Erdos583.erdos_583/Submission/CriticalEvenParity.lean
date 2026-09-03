import Submission.ShortTailCriticalStar
import Submission.FixedRemainderEnergy

/-! Sharp-budget critical edges impose parity restrictions. These restrictions
alone do not exclude an optimized counterexample. -/
namespace Erdos583CriticalEvenParityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.ComponentDeficit
open Erdos583CriticalEndpointCapacityDevelopment
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment Erdos583ShortTailCriticalStarDevelopment
open Erdos583FixedRemainderEnergyDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma sup_edge_neighbor_card {r x : V} (hrx : r ≠ x) (hmiss : ¬H.Adj r x) :
    Nat.card ((H ⊔ edge r x).neighborSet r)=Nat.card (H.neighborSet r)+1 := by
  have he : (H ⊔ edge r x).neighborSet r=insert x (H.neighborSet r) := by
    ext y
    by_cases hy : y=x
    · subst y
      simp [mem_neighborSet,sup_adj,edge_adj,hrx]
    · simp [mem_neighborSet,sup_adj,edge_adj,hy,hrx,eq_comm]
  simp only [Nat.card_coe_set_eq,he,
    Set.ncard_insert_of_notMem (show x ∉ H.neighborSet r from hmiss)]

omit [Fintype V] in
lemma sup_edge_neighbor_card_of_ne {r x z : V} (hzr : z ≠ r) (hzx : z ≠ x) :
    Nat.card ((H ⊔ edge r x).neighborSet z)=Nat.card (H.neighborSet z) := by
  simp only [Nat.card_coe_set_eq]
  congr 1
  ext y
  simp [mem_neighborSet,sup_adj,edge_adj,hzr,hzx]

lemma one_even_missing_edge_not_critical {c x : V}
    (hc : Even (Nat.card (H.neighborSet c)))
    (ho : ∀ z, z ≠ c → Odd (Nat.card (H.neighborSet z)))
    (hcx : c ≠ x) (hmiss : ¬H.Adj c x) (hn : Fintype.card V ≤ 2*p+1) :
    ¬EdgeCritical H p c x := by
  have hxc : Nat.card ((H ⊔ edge c x).neighborSet x)=Nat.card (H.neighborSet x)+1 := by
    rw [edge_comm c x]
    exact sup_edge_neighbor_card hcx.symm (fun hx ↦ hmiss hx.symm)
  have hcc := sup_edge_neighbor_card hcx hmiss
  have hx' : Even (Nat.card ((H ⊔ edge c x).neighborSet x)) := by
    obtain ⟨a,ha⟩ := ho x hcx.symm
    rw [hxc]
    exact ⟨a+1,by omega⟩
  have ho' (z : V) (hzx : z ≠ x) : Odd (Nat.card ((H ⊔ edge c x).neighborSet z)) := by
    by_cases hzc : z=c
    · subst z
      obtain ⟨a,ha⟩ := hc
      rw [hcc]
      exact ⟨a,by omega⟩
    · rw [sup_edge_neighbor_card_of_ne hzc hzx]
      exact ho z hzc
  obtain ⟨D,hD,_,_,hDc⟩ := MarkedBudgets.one_even_path_partition (H ⊔ edge c x) x hx' ho'
  exact fun hf ↦ hf ⟨D,hD,by omega⟩

lemma evenCount_add_even_edge {r x : V} (hrx : r ≠ x) (hmiss : ¬H.Adj r x)
    (hr : Even (Nat.card (H.neighborSet r))) (hx : Even (Nat.card (H.neighborSet x))) :
    evenCount (H ⊔ edge r x)+2=evenCount H := by
  have hr' : Odd (Nat.card ((H ⊔ edge r x).neighborSet r)) := by
    rw [sup_edge_neighbor_card hrx hmiss]
    obtain ⟨a,ha⟩ := hr
    exact ⟨a,by omega⟩
  have hx' : Odd (Nat.card ((H ⊔ edge r x).neighborSet x)) := by
    rw [edge_comm r x,sup_edge_neighbor_card hrx.symm (fun h ↦ hmiss h.symm)]
    obtain ⟨a,ha⟩ := hx
    exact ⟨a,by omega⟩
  let S := {z | Even (Nat.card (H.neighborSet z))}
  have hs : {z | Even (Nat.card ((H ⊔ edge r x).neighborSet z))}=S \ {r,x} := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff]
    by_cases hzr : z=r
    · subst z
      simp only [Nat.not_even_iff_odd.mpr hr',true_or,not_true_eq_false,and_false]
    by_cases hzx : z=x
    · subst z
      simp only [Nat.not_even_iff_odd.mpr hx',or_true,not_true_eq_false,and_false]
    · simp only [sup_edge_neighbor_card_of_ne hzr hzx,S,Set.mem_setOf_eq,hzr,hzx,
        or_self,not_false_eq_true,and_true]
  have hi : ({r,x} : Set V) ⊆ S := by
    rintro z (rfl|rfl) <;> assumption
  have hh := Set.ncard_diff_add_ncard_of_subset hi
  rw [Set.ncard_pair hrx] at hh
  simpa only [evenCount,hs,S] using hh

lemma critical_even_edge_five_even (T : TrailFamily H p) (hp : ∀ j, (T.walk j).IsPath)
    (hn : Fintype.card V=2*p+1) {r x : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r))) (hx : Even (Nat.card (H.neighborSet x)))
    (hc : EdgeCritical H p r x) : 5 ≤ evenCount H := by
  have hm := critical_edge_missing T hp hc
  have hb := evenCount_add_even_edge hrx hm hr hx
  have ho : Odd (evenCount H) := (odd_order_iff_evenCount_odd H).mp ⟨p,hn⟩
  by_contra hlt
  obtain ⟨a,ha⟩ := ho
  have hthree : evenCount H=3 := by omega
  have hone : evenCount (H ⊔ edge r x)=1 := by omega
  obtain ⟨D,hD,hDc⟩ := sharp_one_even_partition (H ⊔ edge r x) hone
  exact hc ⟨D,hD,by omega⟩

lemma odd_one_tail_small_root_many_even (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1)
    (hd : Nat.card (F.graph.neighborSet D.root) ≤ 5) :
    5 ≤ evenCount (remainder F D) := by
  obtain ⟨T,hT,_⟩ := normal_remainder_energy_optimum F D
  have hb := one_tail_odd_ports_degree_ge_seven F D hl T hT
  have he : ∃ x ∈ ports F D, Even (Nat.card ((remainder F D).neighborSet x)) := by
    by_contra hn
    have hh : ∀ x ∈ ports F D, Odd (Nat.card ((remainder F D).neighborSet x)) := by
      intro x hx
      exact Nat.not_even_iff_odd.mp (fun he ↦ hn ⟨x,hx,he⟩)
    have hh' := hb hh
    omega
  obtain ⟨x,hx,hxe⟩ := he
  have hr : Even (Nat.card ((remainder F D).neighborSet D.root)) := by
    apply (QuotaParity.quota_even_iff T D.root).mp
    rw [short_tail_normal_family_quota_zero F D (by omega) T hT]
    exact ⟨0,rfl⟩
  apply critical_even_edge_five_even T hT (r := D.root) (x := x)
    (by simpa only [Fintype.card_fin] using odd_normalBudget F D ho)
    (fun h ↦ root_not_ports F D hl (h.symm ▸ hx)) hr hxe
  exact one_tail_ports_critical F D hl x hx

lemma critical_individual_quota_bound (T : TrailFamily H p)
    (hp : ∀ j, (T.walk j).IsPath) (hn : ∀ j, ¬(T.walk j).Nil)
    {r x : V} (hrx : r ≠ x) (hc : EdgeCritical H p r x) :
    2*T.quota x ≤ Nat.card (H.neighborSet r)+T.quota r := by
  apply quota_bound_of_endpoint_containment T hp hn x r
  exact fun j hj ↦ critical_endpoint_contains T hp hrx (critical_edge_missing T hp hc) hc j hj

lemma nonadjacent_degree_bound {r x : V} (hrx : r ≠ x) (hm : ¬H.Adj r x) :
    Nat.card (H.neighborSet x)+2 ≤ Fintype.card V := by
  have hs : H.neighborSet x ⊆ ({r,x} : Set V)ᶜ := by
    rintro y hy (rfl|rfl)
    · exact hm hy.symm
    · exact H.loopless _ hy
  have hb := Set.ncard_le_ncard hs
  have hc := Set.ncard_add_ncard_compl ({r,x} : Set V)
  rw [Set.ncard_pair hrx,Nat.card_eq_fintype_card] at hc
  rw [Nat.card_coe_set_eq]
  omega

/-- A one-edge tail at a root of degree at most five forces a second
universally inactive, non-universal vertex in the odd connected remainder.
This does not assume the unproved general marking assertion about such pairs. -/
lemma odd_one_tail_small_root_two_unmarkable (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1)
    (hd : Nat.card (F.graph.neighborSet D.root) ≤ 5) :
    ∃ x ∈ ports F D, x ≠ D.root ∧
      Nat.card ((remainder F D).neighborSet D.root)=2 ∧
      Nat.card ((remainder F D).neighborSet x) < 2*normalBudget F D ∧
      ∀ U : TrailFamily (remainder F D) (normalBudget F D),
        (∀ j, (U.walk j).IsPath) → U.quota D.root=0 ∧ U.quota x=0 := by
  obtain ⟨T,hT,_⟩ := normal_remainder_energy_optimum F D
  have hlow := DegreeFourReduction.min_degree_five_of_odd_failure F.smaller ho F.connected F.failure D.root
  have hdeg := normal_root_degree F D
  have hrootdeg : Nat.card ((remainder F D).neighborSet D.root)=2 := by omega
  have he : ∃ x ∈ ports F D, Even (Nat.card ((remainder F D).neighborSet x)) := by
    by_contra hn
    have hh : ∀ x ∈ ports F D, Odd (Nat.card ((remainder F D).neighborSet x)) := by
      intro x hx
      exact Nat.not_even_iff_odd.mp (fun he ↦ hn ⟨x,hx,he⟩)
    have hb := one_tail_odd_ports_degree_ge_seven F D hl T hT hh
    omega
  obtain ⟨x,hx,hxe⟩ := he
  have hxr : x ≠ D.root := fun he ↦ root_not_ports F D hl (he ▸ hx)
  have hcrit := one_tail_ports_critical F D hl x hx
  have hbound := nonadjacent_degree_bound hxr.symm (critical_edge_missing T hT hcrit)
  have hn := odd_normalBudget F D ho
  simp only [Fintype.card_fin] at hbound
  refine ⟨x,hx,hxr,hrootdeg,by omega,?_⟩
  intro U hU
  have hr := short_tail_normal_family_quota_zero F D (by omega) U hU
  have hb := critical_individual_quota_bound U hU (optimal_normal_family_nonnil F D U hU)
    hxr.symm hcrit
  rw [hr,hrootdeg] at hb
  have hxe' := (QuotaParity.quota_even_iff U x).mpr hxe
  obtain ⟨a,ha⟩ := hxe'
  exact ⟨hr,by omega⟩

lemma universally_zero_not_marked {x : V}
    (hz : ∀ U : TrailFamily H p, (∀ j, (U.walk j).IsPath) → U.quota x=0) :
    ¬MarkedCycleGroups.MarkedPartition H p x := by
  rintro ⟨E,b,P,hE,hEc,hP,hn,hPE⟩
  subst p
  obtain ⟨T,hT,hparts⟩ := EdgeDefect.decomposition_path_family E hE
  obtain ⟨j,hj⟩ := hparts P.toSubgraph hPE
  have hdeg : ((T.walk j).toSubgraph.neighborSet x).ncard=1 := by
    rw [hj,hP.neighborSet_toSubgraph_startpoint hn,Set.ncard_singleton]
  have he := ((trail_neighbor_ncard_odd_iff (T.isTrail j) x).mp
    (by rw [hdeg]; exact odd_one)).2
  have hp := DeletionEndpoint.quota_pos_of_endpoint T j he
  rw [hz T hT] at hp
  omega

lemma odd_one_tail_degree_five_marking_obstruction (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1)
    (hd : Nat.card (F.graph.neighborSet D.root) ≤ 5) :
    (remainder F D).Connected ∧ 5 ≤ evenCount (remainder F D) ∧
      ∃ x, x ≠ D.root ∧ Nat.card ((remainder F D).neighborSet D.root)=2 ∧
        Nat.card ((remainder F D).neighborSet D.root) < 2*normalBudget F D ∧
        Nat.card ((remainder F D).neighborSet x) < 2*normalBudget F D ∧
        ¬MarkedCycleGroups.MarkedPartition (remainder F D) (normalBudget F D) D.root ∧
        ¬MarkedCycleGroups.MarkedPartition (remainder F D) (normalBudget F D) x := by
  obtain ⟨x,_,hxr,hrdeg,hxdeg,hzero⟩ := odd_one_tail_small_root_two_unmarkable F D ho hl hd
  have hg := F.graph.degree_lt_card_verts D.root
  have hr := normal_root_degree F D
  have hn := odd_normalBudget F D ho
  simp only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,Nat.card_fin] at hg
  refine ⟨odd_remainder_connected F D ho,odd_one_tail_small_root_many_even F D ho hl hd,
    x,hxr,hrdeg,by omega,hxdeg,?_,?_⟩
  · exact universally_zero_not_marked (fun U hU ↦ (hzero U hU).1)
  · exact universally_zero_not_marked (fun U hU ↦ (hzero U hU).2)

end Erdos583CriticalEvenParityDevelopment
