import Submission.Work

/-! Degree parity for arbitrary indexed trail families, including nil members.
These identities do not provide endpoint-pair transport. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
namespace Erdos583QuotaParityDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma degree_sum {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (v : V) :
    Nat.card (G.neighborSet v) = ∑ i, ((T.walk i).toSubgraph.neighborSet v).ncard := by
  classical
  let N (i : Fin k) := ((T.walk i).toSubgraph.neighborSet v).toFinset
  have he : G.neighborFinset v=Finset.univ.biUnion N := by
    ext w
    simp only [mem_neighborFinset,Finset.mem_biUnion,Finset.mem_univ,true_and]
    simpa only [N,Set.mem_toFinset] using T.cover s(v,w)
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) N := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hi' : (T.walk i).toSubgraph.Adj v w := by simpa only [N,Set.mem_toFinset] using hi
    have hj' : (T.walk j).toSubgraph.Adj v w := by simpa only [N,Set.mem_toFinset] using hj
    exact Set.disjoint_left.mp (T.disjoint hij)
      (show s(v,w) ∈ (T.walk i).toSubgraph.edgeSet from hi') hj'
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,←card_neighborFinset_eq_degree,
    he,Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro i _
  exact (Set.ncard_eq_toFinset_card' _).symm

lemma trail_degree_add_endpoints_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsTrail) (v : V) :
    Even ((p.toSubgraph.neighborSet v).ncard +
      ((if a=v then 1 else 0)+(if b=v then 1 else 0))) := by
  classical
  apply Nat.even_add.mpr
  rw [trail_neighbor_ncard_even_iff hp]
  by_cases ha : a=v <;> by_cases hb : b=v <;> simp_all [eq_comm]

/-- Nil members contribute two endpoint slots and no edges, so they do not
invalidate the parity identity. -/
lemma quota_even_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (v : V) : Even (T.quota v) ↔ Even (Nat.card (G.neighborSet v)) := by
  classical
  have h := Finset.even_sum (s := Finset.univ) (fun i : Fin k ↦
    ((T.walk i).toSubgraph.neighborSet v).ncard +
      ((if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0)))
    (fun i _ ↦ trail_degree_add_endpoints_even (T.walk i) (T.isTrail i) v)
  rw [Finset.sum_add_distrib,←degree_sum T v,←quota_eq_sum_endpoints T v] at h
  exact (Nat.even_add.mp h).symm

lemma quota_odd_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (v : V) : Odd (T.quota v) ↔ Odd (Nat.card (G.neighborSet v)) := by
  simp only [←Nat.not_even_iff_odd,quota_even_iff]

lemma zero_quota_even {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) {v : V} (hv : T.quota v=0) : Even (Nat.card (G.neighborSet v)) := by
  apply (quota_even_iff T v).mp
  simp [hv]

lemma even_root_quota_ge_two {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) {r : V} (hr : HasRoot T r)
    (he : Even (Nat.card (G.neighborSet r))) : 2 ≤ T.quota r := by
  have hp := RootEnergy.root_quota_pos hr
  have hq := (quota_even_iff T r).mpr he
  rw [Nat.even_iff] at hq
  omega

/-- A small root has quota one precisely in the odd-degree case. -/
lemma small_root_quota_one_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) {r : V} (hr : HasRoot T r) (hq : T.quota r ≤ 2) :
    T.quota r=1 ↔ Odd (Nat.card (G.neighborSet r)) := by
  rw [←quota_odd_iff T r,Nat.odd_iff]
  have hp := RootEnergy.root_quota_pos hr
  omega

/-- When the even-degree vertices induce a forest, any rooted single defect
with an available pair can be repaired. The quota-one case is not covered. -/
lemma normalize_root_with_pair_of_even_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r) (hq : 2 ≤ T.quota r)
    (hforest : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic) :
    ∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath := by
  classical
  let c (v : V) := if v=r then T.quota v-2 else T.quota v
  have hquota (v : V) : T.quota v=c v+2*(if r=v then 1 else 0) := by
    by_cases hv : v=r
    · subst v
      simpa [c] using (Nat.sub_add_cancel hq).symm
    · simp [c,hv,Ne.symm hv]
  have hzero (v : V) (hv : c v=0) : Even (Nat.card (G.neighborSet v)) := by
    apply (quota_even_iff T v).mp
    rw [hquota,hv,zero_add]
    exact even_two_mul _
  let f : G.induce {v | c v=0} →g G.induce {v | Even (Nat.card (G.neighborSet v))} :=
    { toFun := fun v ↦ ⟨v.val,hzero v.val v.property⟩
      map_rel' := fun h ↦ h }
  have hinj : Function.Injective f := by
    intro a b hab
    have hh := congrArg (fun z : {v : V // Even (Nat.card (G.neighborSet v))} ↦ z.val) hab
    exact Subtype.ext hh
  have hc : (G.induce {v | c v=0}).IsAcyclic := hforest.comap f hinj
  obtain ⟨_,P,_,hp⟩ := ForestZeroNormalization.normalize_one_defect_forest T c r hs hquota hr hc
  exact ⟨P,hp⟩

lemma normalize_even_root_of_even_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (he : Even (Nat.card (G.neighborSet r)))
    (hforest : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic) :
    ∃ P : TrailFamily G k, ∀ i, (P.walk i).IsPath :=
  normalize_root_with_pair_of_even_forest T r hs hr (even_root_quota_ge_two T hr he) hforest

/-- The remaining obstruction under the even-forest hypothesis is necessarily
an odd-degree root with exactly one endpoint slot. No repair of that case is
asserted here. -/
lemma maximum_root_odd_of_even_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hforest : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic) :
    T.quota r=1 ∧ Odd (Nat.card (G.neighborSet r)) := by
  have hlt : T.quota r<2 := by
    by_contra! hq
    obtain ⟨P,hp⟩ := normalize_root_with_pair_of_even_forest T r hs hr hq hforest
    exact RootEnergy.maximum_defect_no_paths T hs hm P hp
  have hp := RootEnergy.root_quota_pos hr
  have hq : T.quota r=1 := by omega
  refine ⟨hq,(quota_odd_iff T r).mp ?_⟩
  simp [hq]

end Erdos583QuotaParityDevelopment
