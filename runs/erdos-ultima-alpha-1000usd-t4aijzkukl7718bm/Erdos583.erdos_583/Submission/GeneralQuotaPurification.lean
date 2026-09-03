import Submission.NormalQuotaPurification

/-! Refining a path partition realizes any larger endpoint quota of the same
parity, provided the quota does not exceed the vertex degree. -/
namespace Erdos583GeneralQuotaPurificationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.EndpointSelection Erdos583Work.QuotaTrails
open Erdos583NormalForestRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma internal_member_of_endpoint_lt_degree {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {v : V}
    (hv : endpointMultiplicity D v < Nat.card (G.neighborSet v)) :
    ∃ H ∈ D, (H.neighborSet v).ncard=2 := by
  classical
  by_contra hn
  push_neg at hn
  have he (H : G.Subgraph) (hH : H ∈ D) :
      (if (H.neighborSet v).ncard=1 then 1 else 0 : ℕ)=(H.neighborSet v).ncard := by
    have hb := path_neighbor_ncard_le_two (hD.1 H hH) v
    have hh := hn H hH
    split_ifs <;> omega
  have hh : endpointMultiplicity D v=Nat.card (G.neighborSet v) := by
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,hD.2.degree_eq_sum]
    simp only [endpointMultiplicity,Finset.card_filter]
    exact Finset.sum_congr rfl he
  omega

lemma split_at_internal_vertex {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (hne : ∀ H ∈ D, H.edgeSet.Nonempty) {v : V}
    (hv : endpointMultiplicity D v < Nat.card (G.neighborSet v)) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ E.card=D.card+1 ∧
      ∀ x, endpointMultiplicity E x=endpointMultiplicity D x+2*(if x=v then 1 else 0) := by
  classical
  obtain ⟨H,hH,hHv⟩ := internal_member_of_endpoint_lt_degree hD hv
  obtain ⟨a,b,p,hp,rfl⟩ := hD.1 H hH
  have hab := path_endpoints_ne hp (hne _ hH)
  have hpn : ¬p.Nil := Walk.not_nil_of_ne hab
  have hvp : v ∈ p.support := by
    rw [path_neighbor_ncard_formula hp hpn] at hHv
    split_ifs at hHv <;> simp_all
  have hva : v ≠ a := by
    intro hh
    have h1 := (path_neighbor_one_iff hp hpn v).mpr (Or.inl hh)
    omega
  have hvb : v ≠ b := by
    intro hh
    have h1 := (path_neighbor_one_iff hp hpn v).mpr (Or.inr hh)
    omega
  let q := p.takeUntil v hvp
  let r := p.dropUntil v hvp
  have hq : q.IsPath := hp.takeUntil hvp
  have hr : r.IsPath := hp.dropUntil hvp
  have hqn : ¬q.Nil := Walk.not_nil_of_ne hva.symm
  have hrn : ¬r.Nil := Walk.not_nil_of_ne hvb
  have hqne : q.toSubgraph.edgeSet.Nonempty := ⟨s(a,q.snd),q.toSubgraph_adj_snd hqn⟩
  have hrne : r.toSubgraph.edgeSet.Nonempty := ⟨s(v,r.snd),r.toSubgraph_adj_snd hrn⟩
  have hd : Disjoint q.toSubgraph.edgeSet r.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heq her
    exact List.disjoint_left.mp (hp.isTrail.disjoint_edges_takeUntil_dropUntil hvp)
      (q.mem_edges_toSubgraph.mp heq) (r.mem_edges_toSubgraph.mp her)
  have hc : q.toSubgraph.edgeSet ∪ r.toSubgraph.edgeSet=p.toSubgraph.edgeSet := by
    rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append]
    simp only [q,r,Walk.take_spec]
  obtain ⟨hE,hEc,hEn,hEq⟩ := split_member hD hH
    ⟨a,v,q,hq,rfl⟩ ⟨v,b,r,hr,rfl⟩ hqne hrne hd hc hne
  refine ⟨_,hE,hEn,hEc,?_⟩
  intro x
  have hh := hEq x
  simp only [path_neighbor_one_iff hp hpn,path_neighbor_one_iff hq hqn,
    path_neighbor_one_iff hr hrn] at hh
  by_cases hxv : x=v
  · subst x
    simp only [hva,hvb,or_self,↓reduceIte,or_true,true_or] at hh
    simpa only [↓reduceIte,mul_one] using hh
  · by_cases hxa : x=a
    · subst x
      simp only [hxv,hab,or_self,↓reduceIte,true_or] at hh
      simp only [hxv,↓reduceIte,mul_zero,add_zero]
      change endpointMultiplicity _ a+1=endpointMultiplicity D a+1+0 at hh
      omega
    · by_cases hxb : x=b
      · subst x
        simp only [hxv,hxa,or_self,↓reduceIte,or_true] at hh
        simp only [hxv,↓reduceIte,mul_zero,add_zero]
        change endpointMultiplicity _ b+1=endpointMultiplicity D b+0+1 at hh
        omega
      · simp only [hxv,hxa,hxb,or_self,↓reduceIte,add_zero] at hh
        simpa only [hxv,↓reduceIte,mul_zero,add_zero] using hh

lemma realize_larger_quotas (q : V → ℕ)
    (hqdeg : ∀ x, q x ≤ Nat.card (G.neighborSet x))
    (hqpar : ∀ x, Odd (q x) ↔ Odd (Nat.card (G.neighborSet x)))
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hle : ∀ x, endpointMultiplicity D x ≤ q x) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity E x=q x := by
  classical
  generalize hm : (∑ x, q x)-2*D.card=m
  induction m using Nat.strong_induction_on generalizing D with
  | h m ih =>
    by_cases heq : ∀ x, endpointMultiplicity D x=q x
    · exact ⟨D,hD,hne,heq⟩
    obtain ⟨v,hv⟩ := not_forall.mp heq
    have hlt : endpointMultiplicity D v < q v := lt_of_le_of_ne (hle v) hv
    have hpar : Odd (endpointMultiplicity D v) ↔ Odd (q v) := by
      rw [hD.odd_endpointMultiplicity_iff,hqpar]
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    have hstep : endpointMultiplicity D v+2 ≤ q v := by
      simp only [Nat.odd_iff] at hpar
      omega
    obtain ⟨E,hE,hEn,hEc,hEq⟩ := split_at_internal_vertex hD hne (hlt.trans_le (hqdeg v))
    have hEle (x : V) : endpointMultiplicity E x ≤ q x := by
      rw [hEq]
      by_cases hx : x=v
      · simpa only [hx,↓reduceIte,mul_one] using hstep
      · simpa only [hx,↓reduceIte,mul_zero,add_zero] using hle x
    have hsum : 2*E.card ≤ ∑ x, q x := by
      rw [←hE.sum_endpointMultiplicity hEn]
      exact Finset.sum_le_sum (fun x _ ↦ hEle x)
    exact ih ((∑ x,q x)-2*E.card) (by omega) hE hEn hEle rfl

lemma path_family_partition_quota_exact_of_le_degree {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath)
    (hb : ∀ x, T.quota x ≤ Nat.card (G.neighborSet x)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card=k ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity D x=T.quota x := by
  classical
  obtain ⟨D,hD,_,hne,hq⟩ := path_family_partition_quota_le T hp
  obtain ⟨E,hE,hEn,hEq⟩ := realize_larger_quotas T.quota hb
    (fun x ↦ QuotaParity.quota_odd_iff T x) hD hne hq
  refine ⟨E,hE,?_,hEn,hEq⟩
  have hh := hE.sum_endpointMultiplicity hEn
  simp_rw [hEq] at hh
  rw [RootEnergy.sum_quota] at hh
  omega


lemma endpointMultiplicity_le_degree {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (x : V) :
    endpointMultiplicity D x ≤ Nat.card (G.neighborSet x) := by
  classical
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,hD.2.degree_eq_sum]
  simp only [endpointMultiplicity,Finset.card_filter]
  apply Finset.sum_le_sum
  intro H _
  split_ifs <;> omega

lemma path_family_partition_truncated_quota {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧
      ∀ x, endpointMultiplicity D x=min (T.quota x) (Nat.card (G.neighborSet x)) := by
  classical
  obtain ⟨D,hD,_,hne,hq⟩ := path_family_partition_quota_le T hp
  let q (x : V) := min (T.quota x) (Nat.card (G.neighborSet x))
  have hpar (x : V) : Odd (q x) ↔ Odd (Nat.card (G.neighborSet x)) := by
    dsimp only [q]
    rcases le_total (T.quota x) (Nat.card (G.neighborSet x)) with hh|hh
    · rw [min_eq_left hh]
      exact QuotaParity.quota_odd_iff T x
    · rw [min_eq_right hh]
  obtain ⟨E,hE,hEn,hEq⟩ := realize_larger_quotas q (fun x ↦ min_le_right _ _) hpar hD hne
    (fun x ↦ le_min (hq x) (endpointMultiplicity_le_degree hD x))
  refine ⟨E,hE,?_,hEn,hEq⟩
  have hh : (∑ x,endpointMultiplicity E x) ≤ ∑ x,T.quota x := by
    apply Finset.sum_le_sum
    intro x _
    rw [hEq]
    exact min_le_left _ _
  rw [hE.sum_endpointMultiplicity hEn,RootEnergy.sum_quota] at hh
  omega

end Erdos583GeneralQuotaPurificationDevelopment
