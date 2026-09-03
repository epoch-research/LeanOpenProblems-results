import Submission.Work

/-! Incidence and cut-capacity constraints for a rooted single defect.
These are necessary inequalities, not an endpoint-transport theorem. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
namespace Erdos583RootCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma walk_incidence_count {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (v : V) :
    (p.edges.countP fun e ↦ decide (v ∈ e)) +
      ((if a=v then 1 else 0)+(if b=v then 1 else 0)) = 2*p.support.count v := by
  induction p with
  | @nil u =>
    by_cases hu : u=v <;> simp [Walk.support,hu]
  | @cons a x b h p ih =>
    simp only [Walk.edges_cons,Walk.support_cons,List.countP_cons,List.count_cons,
      decide_eq_true_eq,beq_iff_eq,Sym2.mem_iff]
    by_cases ha : a=v <;> by_cases hx : x=v <;>
      simp_all [eq_comm] <;> omega

lemma trail_degree_count {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail) (v : V) :
    (p.toSubgraph.neighborSet v).ncard = p.edges.countP (fun e ↦ decide (v ∈ e)) := by
  classical
  let F := p.toSubgraph.spanningCoe
  have he : F.edgeFinset=p.edges.toFinset := by
    ext e
    simp only [mem_edgeFinset,List.mem_toFinset,←Walk.mem_edges_toSubgraph]
    rfl
  have hd : F.degree v=(p.toSubgraph.neighborSet v).ncard := by
    rw [←neighborSet_ncard]
    rfl
  rw [←hd,←card_incidenceFinset_eq_degree,F.incidenceFinset_eq_filter v,he,
    List.countP_eq_length_filter,←List.toFinset_card_of_nodup (hp.edges_nodup.filter _),
    List.toFinset_filter]
  simp

lemma trail_incidence {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail) (v : V) :
    (p.toSubgraph.neighborSet v).ncard +
      ((if a=v then 1 else 0)+(if b=v then 1 else 0)) = 2*p.support.count v := by
  classical
  rw [trail_degree_count p hp]
  exact walk_incidence_count p v

lemma path_incidence {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (v : V) :
    (p.toSubgraph.neighborSet v).ncard +
      ((if a=v then 1 else 0)+(if b=v then 1 else 0)) = 2*(if v ∈ p.support then 1 else 0) := by
  classical
  rw [trail_incidence p hp.isTrail]
  by_cases hv : v ∈ p.support
  · rw [if_pos hv,List.count_eq_one_of_mem hp.support_nodup hv]
  · rw [if_neg hv,List.count_eq_zero_of_not_mem hv]

lemma repeated_start_incidence {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r x b : V} (h : G.Adj r x) (p : G.Walk x b)
    (hp : p.IsPath) (ht : (Walk.cons h p).IsTrail) (hr : r ∈ p.support) (v : V) :
    ((Walk.cons h p).toSubgraph.neighborSet v).ncard +
      ((if r=v then 1 else 0)+(if b=v then 1 else 0)) =
      2*(if v ∈ (Walk.cons h p).support then 1 else 0)+2*(if r=v then 1 else 0) := by
  classical
  rw [trail_incidence _ ht]
  simp only [Walk.support_cons,List.count_cons,beq_iff_eq,List.mem_cons]
  by_cases hv : v ∈ p.support
  · rw [List.count_eq_one_of_mem hp.support_nodup hv]
    simp [hv,Nat.mul_add]
  · have hrv : r ≠ v := fun he ↦ hv (he ▸ hr)
    rw [List.count_eq_zero_of_not_mem hv]
    simp [hv,hrv,Ne.symm hrv]

lemma rooted_member_incidence {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r) :
    ∃ i : Fin k, ∀ j v,
      ((T.walk j).toSubgraph.neighborSet v).ncard +
        ((if T.start j=v then 1 else 0)+(if T.finish j=v then 1 else 0)) =
        2*(if v ∈ (T.walk j).support then 1 else 0)+2*(if j=i ∧ r=v then 1 else 0) := by
  classical
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  have hx : (R.tail ρ).toSubgraph.Adj r (R.tail ρ).snd := by
    have hh := (R.tail ρ).toSubgraph_adj_snd hn
    simpa only [hρ] using hh
  obtain ⟨i,b,h,p,_,hends,ht,he,hrep⟩ := rooted_exposed_rep R ρ hρ hx
  obtain ⟨hp,_,hothers⟩ := simple_tail_of_one_defect_rep T hs i h p ht he hrep
  refine ⟨i,?_⟩
  intro j v
  by_cases hji : j=i
  · subst j
    have hh := repeated_start_incidence h p hp ht hrep v
    have hm : v ∈ (T.walk i).support ↔ v ∈ (Walk.cons h p).support := by
      rw [←Walk.mem_verts_toSubgraph,he,Walk.mem_verts_toSubgraph]
    simp only [he,hm]
    rcases hends with ⟨ha,hb⟩|⟨ha,hb⟩
    · simpa only [ha,hb,true_and] using hh
    · simpa only [ha,hb,true_and,Nat.add_comm] using hh
  · simpa only [hji,false_and,if_false,mul_zero,add_zero] using
      path_incidence (T.walk j) (hothers j hji) v

/-- All repeated-vertex excess is localized at the root. Nil members are
allowed and contribute one incidence and two endpoint slots at their vertex. -/
lemma rooted_incidence {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (v : V) :
    Nat.card (G.neighborSet v)+T.quota v =
      2*(Finset.univ.filter fun i ↦ v ∈ (T.walk i).support).card + 2*(if r=v then 1 else 0) := by
  classical
  obtain ⟨i,hi⟩ := rooted_member_incidence T r hs hr
  rw [QuotaParity.degree_sum T v,quota_eq_sum_endpoints T v,←Finset.sum_add_distrib]
  simp_rw [hi]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.card_filter]
  congr 1
  by_cases hv : r=v <;> simp [hv]

lemma rooted_degree_quota_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (v : V) : Nat.card (G.neighborSet v)+T.quota v ≤ 2*k+2*(if r=v then 1 else 0) := by
  classical
  rw [rooted_incidence T r hs hr]
  have hc := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin k ↦ v ∈ (T.walk i).support)
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  omega

/-- An over-capacity vertex pins every rooted single defect to that vertex. -/
lemma root_eq_of_over_capacity {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (v : V) (hv : 2*k < Nat.card (G.neighborSet v)+T.quota v) : r=v := by
  by_contra hn
  have hh := rooted_degree_quota_bound T r hs hr v
  simp only [if_neg hn,mul_zero,add_zero] at hh
  omega

/-- The endpoint-versus-boundary argument needs a trail, not a simple path. -/
lemma trail_endpoint_boundary_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {a b v : V} (p : G.Walk a b) (hp : p.IsTrail)
    (hv : v ∈ p.support) (hvs : v ∉ S) :
    (if a ∈ S then 1 else 0)+(if b ∈ S then 1 else 0) ≤
      (p.toSubgraph.edgeSet ∩ (boundaryGraph G S).edgeSet).ncard := by
  classical
  let p₁ := p.takeUntil v hv
  let p₂ := p.dropUntil v hv
  let C := (boundaryGraph G S).edgeSet
  have hc₁ : (if a ∈ S then 1 else 0) ≤ (p₁.toSubgraph.edgeSet ∩ C).ncard := by
    split_ifs with ha
    · exact (Set.ncard_pos (Set.toFinite _)).mpr (walk_boundary_nonempty S p₁ ha hvs)
    · omega
  have hc₂ : (if b ∈ S then 1 else 0) ≤ (p₂.toSubgraph.edgeSet ∩ C).ncard := by
    split_ifs with hb
    · have hh := (Set.ncard_pos (Set.toFinite _)).mpr (walk_boundary_nonempty S p₂.reverse hb hvs)
      simpa [C] using hh
    · omega
  have hd : Disjoint (p₁.toSubgraph.edgeSet ∩ C) (p₂.toSubgraph.edgeSet ∩ C) := by
    apply Set.disjoint_left.mpr
    intro e he₁ he₂
    exact List.disjoint_left.mp (hp.disjoint_edges_takeUntil_dropUntil hv)
      (p₁.mem_edges_toSubgraph.mp he₁.1) (p₂.mem_edges_toSubgraph.mp he₂.1)
  have he : p.toSubgraph.edgeSet=p₁.toSubgraph.edgeSet ∪ p₂.toSubgraph.edgeSet := by
    rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append]
    simp only [p₁,p₂,Walk.take_spec]
  rw [he,Set.union_inter_distrib_right,Set.ncard_union_eq hd]
  exact Nat.add_le_add hc₁ hc₂

lemma ncard_inter_eq_sum {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (C : Set (Sym2 V)) :
    (G.edgeSet ∩ C).ncard=∑ i, ((T.walk i).toSubgraph.edgeSet ∩ C).ncard := by
  classical
  let E (i : Fin k) := ((T.walk i).toSubgraph.edgeSet ∩ C).toFinset
  have he : (G.edgeSet ∩ C).toFinset=Finset.univ.biUnion E := by
    ext e
    simp only [Set.mem_toFinset,Set.mem_inter_iff,Finset.mem_biUnion,Finset.mem_univ,true_and,E]
    rw [T.cover]
    aesop
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) E := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hi hj
    have hi' : e ∈ (T.walk i).toSubgraph.edgeSet ∩ C := by simpa only [E,Set.mem_toFinset] using hi
    have hj' : e ∈ (T.walk j).toSubgraph.edgeSet ∩ C := by simpa only [E,Set.mem_toFinset] using hj
    exact Set.disjoint_left.mp (T.disjoint hij) hi'.1 hj'.1
  rw [Set.ncard_eq_toFinset_card',he,Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro i _
  exact (Set.ncard_eq_toFinset_card' _).symm

/-- The degree/endpoint cut bound has exactly two units of slack at the
repeated root and no slack at other vertices. -/
lemma rooted_cut_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (S : Finset V) (v : V) (hv : v ∉ S) :
    Nat.card (G.neighborSet v)+T.quota v+∑ w ∈ S, T.quota w ≤
      2*k+(boundaryGraph G (S : Set V)).edgeSet.ncard+2*(if r=v then 1 else 0) := by
  classical
  obtain ⟨i,hi⟩ := rooted_member_incidence T r hs hr
  let C := (boundaryGraph G (S : Set V)).edgeSet
  have hlocal (j : Fin k) :
      ((T.walk j).toSubgraph.neighborSet v).ncard +
        ((if T.start j=v then 1 else 0)+(if T.finish j=v then 1 else 0)) +
        (∑ w ∈ S, ((if T.start j=w then 1 else 0)+(if T.finish j=w then 1 else 0))) ≤
        2+((T.walk j).toSubgraph.edgeSet ∩ C).ncard+2*(if j=i ∧ r=v then 1 else 0) := by
    rw [hi j v,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq]
    by_cases hvm : v ∈ (T.walk j).support
    · have hh := trail_endpoint_boundary_bound (S : Set V) (T.walk j) (T.isTrail j) hvm hv
      rw [if_pos hvm]
      simp only [Finset.mem_coe] at hh
      dsimp only [C] at *
      omega
    · rw [if_neg hvm]
      split_ifs <;> omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hlocal j)
  have hsub : C ⊆ G.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h a b => exact he.1
  have hC := ncard_inter_eq_sum T C
  rw [Set.inter_eq_right.mpr hsub] at hC
  have hend : ∑ w ∈ S, T.quota w = ∑ j, ∑ w ∈ S,
      ((if T.start j=w then 1 else 0)+(if T.finish j=w then 1 else 0)) := by
    simp_rw [quota_eq_sum_endpoints]
    rw [Finset.sum_comm]
  have hroot : ∑ j : Fin k, 2*(if j=i ∧ r=v then 1 else 0)=2*(if r=v then 1 else 0) := by
    by_cases hrv : r=v <;> simp [hrv]
  have hquota := quota_eq_sum_endpoints T v
  simp only [Finset.sum_add_distrib] at hh hquota hend
  rw [←QuotaParity.degree_sum T v,←hquota,←hend,←hC,hroot] at hh
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm] using hh

lemma root_eq_of_cut_over_capacity {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (S : Finset V) (v : V) (hv : v ∉ S)
    (hcap : 2*k+(boundaryGraph G (S : Set V)).edgeSet.ncard <
      Nat.card (G.neighborSet v)+T.quota v+∑ w ∈ S, T.quota w) : r=v := by
  by_contra hn
  have hh := rooted_cut_bound T r hs hr S v hv
  simp only [if_neg hn,mul_zero,add_zero] at hh
  omega

end Erdos583RootCapacityDevelopment
