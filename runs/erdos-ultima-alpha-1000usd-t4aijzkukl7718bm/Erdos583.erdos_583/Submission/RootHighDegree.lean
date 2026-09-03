import Submission.Work

/-! A degree-two defect root can be moved to a higher-degree neighbor without
changing the incidence score or the minimum endpoint-quota energy. -/
namespace Erdos583RootHighDegreeDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1600000

lemma degree_two_root_is_cycle {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hr : HasRoot T r) (hd : Nat.card (G.neighborSet r)=2) :
    ∃ i : Fin k, ∃ C : G.Walk r r, T.start i=r ∧ T.finish i=r ∧ C.IsCycle ∧
      (T.walk i).toSubgraph=C.toSubgraph := by
  classical
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  have hx : (R.tail ρ).toSubgraph.Adj r (R.tail ρ).snd := by
    simpa only [hρ] using (R.tail ρ).toSubgraph_adj_snd hn
  obtain ⟨i,b,h,p,_,hends,ht,he,hrep⟩ := rooted_exposed_rep R ρ hρ hx
  obtain ⟨hp,_,_⟩ := simple_tail_of_one_defect_rep T hs i h p ht he hrep
  have hlocal := RootCapacity.repeated_start_incidence h p hp ht hrep r
  have hcap : (Walk.cons h p).toSubgraph.neighborSet r ⊆ G.neighborSet r :=
    fun _ hh ↦ (Walk.cons h p).toSubgraph.adj_sub hh
  have hcard := Set.ncard_le_ncard hcap
  rw [show (G.neighborSet r).ncard=2 by simpa only [Nat.card_coe_set_eq] using hd] at hcard
  have hb : b=r := by
    by_contra hb
    simp only [if_neg hb,Walk.support_cons,List.mem_cons,true_or,if_true] at hlocal
    omega
  subst b
  have hc : (Walk.cons h p).IsCycle := (Walk.cons_isCycle_iff p h).mpr
    ⟨hp,(Walk.isTrail_cons h p).mp ht |>.2⟩
  rcases hends with ⟨ha,hb⟩|⟨hb,ha⟩ <;> exact ⟨i,Walk.cons h p,ha,hb,hc,he⟩

lemma root_degree_ge_two {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r) :
    2 ≤ Nat.card (G.neighborSet r) := by
  obtain ⟨x,y,hxy,hrx,hry,_,_⟩ := RootEnergy.two_zero_neighbors T r hs hm hr
  rw [Nat.card_coe_set_eq]
  have hh := (Set.one_lt_ncard_iff (Set.toFinite (G.neighborSet r))).mpr ⟨x,y,hrx,hry,hxy⟩
  omega

lemma move_degree_two_root {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r)
    (hq : T.quota r=2) (hd : Nat.card (G.neighborSet r)=2) :
    ∃ U : TrailFamily G k, ∃ x : Fin n, U.score=T.score ∧ HasRoot U x ∧
      U.quota x=2 ∧ RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T ∧
      4 ≤ Nat.card (G.neighborSet x) := by
  obtain ⟨i,C,hai,hbi,hC,hi⟩ := degree_two_root_is_cycle T r hs hr hd
  obtain ⟨x,y,hxy,hrx,hry,hx,_⟩ := RootEnergy.two_zero_neighbors T r hs hm hr
  have hN : C.toSubgraph.neighborSet r=G.neighborSet r := by
    apply Set.eq_of_subset_of_ncard_le (fun _ hh ↦ C.toSubgraph.adj_sub hh)
    change (G.neighborSet r).ncard ≤ (C.toSubgraph.neighborSet r).ncard
    rw [hC.ncard_neighborSet_toSubgraph_eq_two C.start_mem_support,←Nat.card_coe_set_eq,hd]
  have hxr : C.toSubgraph.Adj r x := by change x ∈ C.toSubgraph.neighborSet r; rw [hN]; exact hrx
  have hxC : x ∈ C.support := Walk.mem_support_of_adj_toSubgraph hxr.symm
  obtain ⟨U,hUs,hUr,hUq⟩ := reroot_closed_member T i hai hbi C hC.isTrail hC.not_nil hi.symm hxC
  have hUx : U.quota x=2 := by
    have hh := hUq x
    simp only [if_neg hrx.ne,mul_zero,add_zero,hx,zero_add] at hh
    exact hh
  have henergy := RootEnergy.pair_energy_balance T.quota U.quota r x hrx.ne hx hUq
  have hE : RootEnergy.quotaEnergy U=RootEnergy.quotaEnergy T := by
    change RootEnergy.quotaEnergy U+4*T.quota r=RootEnergy.quotaEnergy T+8 at henergy
    rw [hq] at henergy
    omega
  exact ⟨U,x,hUs,hUr,hUx,hE,LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hrx hd⟩

/-- The minimum-energy root can be chosen of degree at least three. Thus an
even-degree selected root has degree at least four, not two. This leaves
cubic odd roots and higher-degree roots unresolved. -/
lemma exists_small_quota_high_degree_root {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r) :
    ∃ (S : TrailFamily G k) (s : Fin n), S.score=T.score ∧ HasRoot S s ∧
      (∀ U : TrailFamily G k, U.score ≤ S.score) ∧
      (S.quota s=1 ∨ S.quota s=2) ∧ 3 ≤ Nat.card (G.neighborSet s) ∧
      (∀ (U : TrailFamily G k) (u : Fin n), U.score=S.score → HasRoot U u →
        RootEnergy.quotaEnergy S ≤ RootEnergy.quotaEnergy U) := by
  obtain ⟨S,s,hSs,hSr,hSm,hq,hmin⟩ := RootEnergy.exists_small_root_quota T r hs hm hr
  have hscore : S.score+1=G.edgeSet.ncard+k := by omega
  by_cases hd : Nat.card (G.neighborSet s)=2
  · have he : Even (S.quota s) := (QuotaParity.quota_even_iff S s).mpr (by rw [hd]; decide)
    have hq2 : S.quota s=2 := by rcases he with ⟨m,hm⟩; omega
    obtain ⟨U,u,hUs,hUr,hUq,hUE,hdegree⟩ := move_degree_two_root hsmall hG hfail S s hscore hSm hSr hq2 hd
    refine ⟨U,u,hUs.trans hSs,hUr,(fun W ↦ (hSm W).trans (by omega)),Or.inr hUq,by omega,?_⟩
    intro W w hWs hWr
    rw [hUE]
    exact hmin W w (hWs.trans hUs) hWr
  · have h2 := root_degree_ge_two S s hscore hSm hSr
    exact ⟨S,s,hSs,hSr,hSm,hq,by omega,hmin⟩


lemma small_quota_high_degree_cases {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hq : T.quota r=1 ∨ T.quota r=2)
    (hd : 3 ≤ Nat.card (G.neighborSet r)) :
    (T.quota r=1 ∧ Odd (Nat.card (G.neighborSet r)) ∧ 3 ≤ Nat.card (G.neighborSet r)) ∨
      (T.quota r=2 ∧ Even (Nat.card (G.neighborSet r)) ∧ 4 ≤ Nat.card (G.neighborSet r)) := by
  rcases hq with hq|hq
  · exact Or.inl ⟨hq,(QuotaParity.quota_odd_iff T r).mp (by rw [hq]; decide),hd⟩
  · have he := (QuotaParity.quota_even_iff T r).mp (show Even (T.quota r) by rw [hq]; decide)
    refine Or.inr ⟨hq,he,?_⟩
    obtain ⟨m,hm⟩ := he
    omega

end Erdos583RootHighDegreeDevelopment
