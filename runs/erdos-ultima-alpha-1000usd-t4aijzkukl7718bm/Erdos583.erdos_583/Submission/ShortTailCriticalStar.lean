import Submission.CriticalEndpointCapacity
import Submission.UniversalNormalEndpoints

/-! The three critical edges at a one-edge-tail root give universal
endpoint-capacity inequalities, without a restriction on cycle length. -/
namespace Erdos583ShortTailCriticalStarDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583UniversalNormalEndpointsDevelopment Erdos583CriticalEndpointCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

abbrev ports : Finset (Fin F.order) :=
  {D.rep.cycle.snd,D.rep.cycle.penultimate,D.rep.finish}

lemma one_tail_penultimate (hl : D.rep.tail.length=1) : D.rep.tail.penultimate=D.root := by
  simp only [Walk.penultimate,hl,Nat.sub_self,Walk.getVert_zero]

lemma one_tail_finish_not_cycle (hl : D.rep.tail.length=1) : D.rep.finish ∉ D.rep.cycle.support := by
  intro h
  have he := D.rep.inter D.rep.finish h D.rep.tail.end_mem_support
  exact (Walk.adj_of_length_eq_one hl).ne he.symm

lemma one_tail_ports_card (hl : D.rep.tail.length=1) : (ports F D).card=3 := by
  have hxy := D.rep.isCycle.snd_ne_penultimate
  have htx : D.rep.finish ≠ D.rep.cycle.snd := fun h ↦ one_tail_finish_not_cycle F D hl
    (h.symm ▸ D.rep.cycle.getVert_mem_support 1)
  have hty : D.rep.finish ≠ D.rep.cycle.penultimate := fun h ↦ one_tail_finish_not_cycle F D hl
    (h.symm ▸ D.rep.cycle.getVert_mem_support (D.rep.cycle.length-1))
  simp [ports,hxy,htx.symm,hty.symm]

lemma root_not_ports (hl : D.rep.tail.length=1) : D.root ∉ ports F D := by
  have hx := (D.rep.cycle.toSubgraph_adj_snd D.rep.isCycle.not_nil).ne
  have hy := (D.rep.cycle.toSubgraph_adj_penultimate D.rep.isCycle.not_nil).ne.symm
  have ht := (Walk.adj_of_length_eq_one hl).ne
  simp [ports,hx,hy,ht]

lemma one_tail_ports_critical (hl : D.rep.tail.length=1) :
    ∀ x ∈ ports F D, EdgeCritical (remainder F D) (normalBudget F D) D.root x := by
  intro x hx
  rcases (show x=D.rep.cycle.snd ∨ x=D.rep.cycle.penultimate ∨ x=D.rep.finish from by simpa [ports] using hx)
    with rfl|rfl|rfl
  · exact root_cycle_edge_critical F D (D.rep.cycle.toSubgraph_adj_snd D.rep.isCycle.not_nil)
  · exact root_cycle_edge_critical F D ((D.rep.cycle.toSubgraph_adj_penultimate D.rep.isCycle.not_nil).symm)
  · have hc : EdgeCritical (remainder F D) (normalBudget F D) D.rep.finish D.rep.tail.penultimate :=
      last_tail_edge_critical F D
    rw [one_tail_penultimate F D hl] at hc
    exact hc.symm

lemma one_tail_ports_quota_bound (hl : D.rep.tail.length=1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath) :
    (∑ x ∈ ports F D, T.quota x)+3 ≤ Nat.card (F.graph.neighborSet D.root) := by
  have hc := one_tail_ports_critical F D hl
  have hb := critical_neighbor_quota_bound T hp D.root (ports F D) (root_not_ports F D hl)
    (fun x hx ↦ critical_edge_missing T hp (hc x hx)) hc
  have hd := normal_root_degree F D
  omega

lemma one_tail_three_quota_bound (hl : D.rep.tail.length=1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath) :
    T.quota D.rep.cycle.snd+T.quota D.rep.cycle.penultimate+T.quota D.rep.finish+3 ≤
      Nat.card (F.graph.neighborSet D.root) := by
  have hxy := D.rep.isCycle.snd_ne_penultimate
  have htx : D.rep.finish ≠ D.rep.cycle.snd := fun h ↦ one_tail_finish_not_cycle F D hl
    (h.symm ▸ D.rep.cycle.getVert_mem_support 1)
  have hty : D.rep.finish ≠ D.rep.cycle.penultimate := fun h ↦ one_tail_finish_not_cycle F D hl
    (h.symm ▸ D.rep.cycle.getVert_mem_support (D.rep.cycle.length-1))
  have hb := one_tail_ports_quota_bound F D hl T hp
  simpa only [ports,Finset.sum_insert (show D.rep.cycle.snd ∉ ({D.rep.cycle.penultimate,D.rep.finish} : Finset _) by simp [hxy,htx.symm]),
    Finset.sum_insert (show D.rep.cycle.penultimate ∉ ({D.rep.finish} : Finset _) by simp [hty.symm]),
    Finset.sum_singleton,←Nat.add_assoc] using hb

lemma one_tail_odd_ports_degree_bound (hl : D.rep.tail.length=1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (ho : ∀ x ∈ ports F D, Odd (Nat.card ((remainder F D).neighborSet x))) :
    6 ≤ Nat.card (F.graph.neighborSet D.root) := by
  have hc := one_tail_ports_critical F D hl
  have hb := critical_odd_neighbors_bound T hp D.root (ports F D) (root_not_ports F D hl)
    (fun x hx ↦ critical_edge_missing T hp (hc x hx)) hc ho
  rw [one_tail_ports_card F D hl] at hb
  have hd := normal_root_degree F D
  omega



lemma one_tail_odd_ports_degree_ge_seven (hl : D.rep.tail.length=1)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath)
    (ho : ∀ x ∈ ports F D, Odd (Nat.card ((remainder F D).neighborSet x))) :
    7 ≤ Nat.card (F.graph.neighborSet D.root) := by
  have hb := one_tail_odd_ports_degree_bound F D hl T hp ho
  have hq := Erdos583RootEndpointTailCapacityDevelopment.minimum_one_edge_tail_root_quota_one
    D.family D.score D.maximum D.root D.rep D.cycle_minimum hl
  have hodd : Odd (Nat.card (F.graph.neighborSet D.root)) :=
    (QuotaParity.quota_odd_iff D.family D.root).mp (by rw [hq]; exact odd_one)
  obtain ⟨a,ha⟩ := hodd
  omega

lemma cubic_one_tail_ports_quota_zero (hl : D.rep.tail.length=1)
    (hd : Nat.card (F.graph.neighborSet D.root)=3)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath) :
    ∀ x ∈ ports F D, T.quota x=0 := by
  have hb := one_tail_ports_quota_bound F D hl T hp
  rw [hd] at hb
  have hs : (∑ x ∈ ports F D, T.quota x)=0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hs

lemma cubic_one_tail_ports_even (hl : D.rep.tail.length=1)
    (hd : Nat.card (F.graph.neighborSet D.root)=3)
    (T : TrailFamily (remainder F D) (normalBudget F D)) (hp : ∀ j, (T.walk j).IsPath) :
    ∀ x ∈ ports F D, Even (Nat.card ((remainder F D).neighborSet x)) := by
  intro x hx
  exact (QuotaParity.quota_even_iff T x).mp (by
    rw [cubic_one_tail_ports_quota_zero F D hl hd T hp x hx]
    exact ⟨0,rfl⟩)

end Erdos583ShortTailCriticalStarDevelopment
