import Submission.MatchingCutGlue

/-! Marked contraction centers save two paths across an even matching cut. -/
namespace Erdos583MatchingCutMarkedDevelopment
open SimpleGraph Erdos583Work Erdos583MatchingCutGlueDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.BridgeGlue
open Erdos583Work.StarPathPieces Erdos583Work.StarContraction
open Erdos583Work.BoundaryPorts
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}

lemma lift_marked_contraction {r : V} (hr : r ∈ S) {b : ℕ}
    (hmark : ∃ D : Finset ((contract G S r hr).induce (Sᶜ ∪ {r})).Subgraph,
      GoodDecomposition _ D ∧ D.card ≤ b ∧
        MarkedDouble.MarkedAt D ⟨r,Or.inr rfl⟩) :
    ∃ k, ∃ T : TrailFamily (contract G S r hr) k,
      (∀ i, (T.walk i).IsPath) ∧ k ≤ b ∧ 0 < T.quota r := by
  let K := contract G S r hr
  let R := Sᶜ ∪ {r}
  obtain ⟨D,hD,hDc,a,p,hp,hpD⟩ := hmark
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := MarkedBudgets.lift_induce_marked R hD p hp hpD
  have hKR : within K R=K := within_eq G S r hr
  have hex : ∃ E : Finset K.Subgraph, ∃ q : K.Walk r a.val,
      GoodDecomposition K E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card := by
    exact Eq.mp (congrArg (fun J : SimpleGraph V ↦
      ∃ F : Finset J.Subgraph, ∃ q : J.Walk r a.val,
        GoodDecomposition J F ∧ q.IsPath ∧ q.toSubgraph ∈ F ∧ F.card ≤ D.card) hKR)
      ⟨E,q,hE,hq,hqm,hEc⟩
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := hex
  obtain ⟨T,hT,hparts⟩ := EdgeDefect.decomposition_path_family E hE
  obtain ⟨i,hi⟩ := hparts q.toSubgraph hqm
  have hend := MarkedBudgets.endpoint_of_path_rep q hq (T.walk i) (T.isTrail i) hi
  exact ⟨E.card,T,hT,hEc.trans hDc,DeletionEndpoint.quota_pos_of_endpoint T i hend⟩

lemma marked_contraction_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected) {r : V} (hr : r ∈ S)
    (hs : 3 ≤ S.ncard) :
    ∃ k, ∃ T : TrailFamily (contract G S r hr) k,
      (∀ i, (T.walk i).IsPath) ∧ k ≤ ⌈((Sᶜ.ncard+2 : ℕ) : ℚ)/2⌉₊ ∧ 0 < T.quota r := by
  let K := contract G S r hr
  let R := Sᶜ ∪ {r}
  have hc : R.ncard+S.ncard=Fintype.card V+1 := card_vertices S r hr
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hsum
  have hR : R.ncard=Sᶜ.ncard+1 := by omega
  have hcard : Fintype.card R=R.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,a,p,hD,hp,hpD,hDc⟩ := CutVertexReduction.smaller_order_marked hsmall
    (K.induce R) (connected_induce G S r hr hG) ⟨r,Or.inr rfl⟩ (by omega)
  apply lift_marked_contraction hr
  refine ⟨D,hD,?_,a,p,hp,hpD⟩
  simpa only [hcard,hR,Nat.add_assoc] using hDc

lemma marked_even_matching_glue {r t : V} (hr : r ∈ S) (ht : t ∈ Sᶜ)
    {k l : ℕ} (T : TrailFamily (contract G S r hr) k)
    (U : TrailFamily (contract G Sᶜ t ht) l)
    (hT : ∀ i, (T.walk i).IsPath) (hU : ∀ i, (U.walk i).IsPath)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (heven : Even (Fintype.card (Boundary G S))) (hmT : 0 < T.quota r) (hmU : 0 < U.quota t) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card+2 ≤ k+l := by
  have hi' : Function.Injective (outer G Sᶜ) := by
    intro b c he
    obtain ⟨b,rfl⟩ := flip_surjective b
    obtain ⟨c,rfl⟩ := flip_surjective c
    exact congrArg Erdos583MatchingCutGlueDevelopment.flip (hi he)
  have he : Fintype.card (Boundary G Sᶜ)=Fintype.card (Boundary G S) :=
    (Fintype.card_congr (Equiv.ofBijective _ ⟨flip_injective,flip_surjective⟩)).symm
  have hqT : Even (T.quota r) := (QuotaParity.quota_even_iff T r).mpr (by
    rw [boundary_degree hr ho]
    simpa only [←Nat.card_eq_fintype_card] using heven)
  have hqU : Even (U.quota t) := (QuotaParity.quota_even_iff U t).mpr (by
    rw [boundary_degree ht hi']
    simp only [←Nat.card_eq_fintype_card] at he heven ⊢
    rwa [he])
  apply matching_glue_saving hr ht T U hT hU hi ho 2
  obtain ⟨a,ha⟩ := hqT
  obtain ⟨b,hb⟩ := hqU
  omega

lemma twice_marked_budget (a b : ℕ) (hpar : Even a ∨ Even b) :
    ⌈((a+2 : ℕ) : ℚ)/2⌉₊+⌈((b+2 : ℕ) : ℚ)/2⌉₊ ≤ ⌈((a+b : ℕ) : ℚ)/2⌉₊+2 := by
  simp only [ceil_half]
  rcases hpar with ⟨k,hk⟩|⟨k,hk⟩ <;> omega

lemma even_matching_cut_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (heven : Even (Fintype.card (Boundary G S))) (hpar : Even S.ncard ∨ Even Sᶜ.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite S)).mp (by omega : 0 < S.ncard)
  obtain ⟨t,htS⟩ := (Set.ncard_pos (Set.toFinite Sᶜ)).mp (by omega : 0 < Sᶜ.ncard)
  obtain ⟨k,T,hT,hk,hmT⟩ := marked_contraction_partition hsmall hn hG hr hs
  obtain ⟨l,U,hU,hl,hmU⟩ := marked_contraction_partition hsmall hn hG htS ht
  obtain ⟨D,hD,hDc⟩ := marked_even_matching_glue hr htS T U hT hU hi ho heven hmT hmU
  have hb := twice_marked_budget S.ncard Sᶜ.ncard hpar
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hsum
  simp only [compl_compl] at hl
  rw [hsum] at hb
  exact ⟨D,hD,by omega⟩

lemma failure_even_matching_cut_odd_sides {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (heven : Even (Fintype.card (Boundary G S))) : Odd S.ncard ∧ Odd Sᶜ.ncard := by
  have hp : ¬(Even S.ncard ∨ Even Sᶜ.ncard) := fun hpar ↦
    hfail (even_matching_cut_reduction hsmall hn hG hs ht hi ho heven hpar)
  exact ⟨Nat.not_even_iff_odd.mp (fun h ↦ hp (Or.inl h)),
    Nat.not_even_iff_odd.mp (fun h ↦ hp (Or.inr h))⟩

lemma odd_failure_no_matching_cut {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected) (hnodd : Odd n)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) : False := by
  have he := odd_failure_no_odd_matching_cut hsmall hn hG hnodd hfail (by omega) (by omega) hi ho
  obtain ⟨hoS,hoT⟩ := failure_even_matching_cut_odd_sides hsmall hn hG hfail hs ht hi ho he
  have hp := hoS.add_odd hoT
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card,hn] at hsum
  rw [hsum] at hp
  exact (Nat.not_even_iff_odd.mpr hnodd) hp

lemma degree_le_matching_side (hi : Function.Injective (inner G S)) {x : V} (hx : x ∈ S) :
    Nat.card (G.neighborSet x) ≤ S.ncard := by
  let f : G.neighborSet x → S := fun y ↦ if hy : y.val ∈ S then ⟨y.val,hy⟩ else ⟨x,hx⟩
  have hf : Function.Injective f := by
    intro y z he
    have he' := congrArg (fun v : S ↦ v.val) he
    by_cases hy : y.val ∈ S <;> by_cases hz : z.val ∈ S
    · exact Subtype.ext (by simpa only [f,dif_pos hy,dif_pos hz] using he')
    · have heq : y.val=x := by simpa only [f,dif_pos hy,dif_neg hz] using he'
      exact (y.property.ne heq.symm).elim
    · have heq : z.val=x := by simpa only [f,dif_neg hy,dif_pos hz] using he'.symm
      exact (z.property.ne heq.symm).elim
    · let b : Boundary G S := ⟨(⟨x,hx⟩,⟨y.val,hy⟩),y.property⟩
      let c : Boundary G S := ⟨(⟨x,hx⟩,⟨z.val,hz⟩),z.property⟩
      exact Subtype.ext (congrArg (outer G S) (hi (show inner G S b=inner G S c from rfl)))
  have hh := Fintype.card_le_of_injective f hf
  simpa only [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh

lemma odd_failure_no_proper_matching_cut {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) (hnodd : Odd n)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) (hs : S.Nonempty) (ht : Sᶜ.Nonempty)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) : False := by
  obtain ⟨x,hx⟩ := hs
  obtain ⟨y,hy⟩ := ht
  have hxdeg := DegreeFourReduction.min_degree_five_of_odd_failure hsmall hnodd hG hfail x
  have hydeg := DegreeFourReduction.min_degree_five_of_odd_failure hsmall hnodd hG hfail y
  have hxbound := degree_le_matching_side hi hx
  have ho' : Function.Injective (inner G Sᶜ) := by
    intro b c he
    obtain ⟨b,rfl⟩ := flip_surjective b
    obtain ⟨c,rfl⟩ := flip_surjective c
    exact congrArg Erdos583MatchingCutGlueDevelopment.flip (ho he)
  have hybound := degree_le_matching_side ho' hy
  exact odd_failure_no_matching_cut hsmall (Fintype.card_fin n) hG hnodd hfail
    (by omega) (by omega) hi ho

lemma failure_matching_cut_parity {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) :
    Even n ∧ (Even (Fintype.card (Boundary G S)) ↔ Odd S.ncard) ∧
      (Even S.ncard ↔ Even Sᶜ.ncard) := by
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card,hn] at hsum
  by_cases he : Even (Fintype.card (Boundary G S))
  · obtain ⟨ha,hb⟩ := failure_even_matching_cut_odd_sides hsmall hn hG hfail hs ht hi ho he
    have hnE := ha.add_odd hb
    rw [hsum] at hnE
    exact ⟨hnE,⟨fun _ ↦ ha,fun _ ↦ he⟩,
      ⟨fun h ↦ ((Nat.not_even_iff_odd.mpr ha) h).elim,
        fun h ↦ ((Nat.not_even_iff_odd.mpr hb) h).elim⟩⟩
  · obtain ⟨ha,hb⟩ := failure_odd_matching_cut_even_sides hsmall hn hG hfail
      (by omega) (by omega) hi ho (Nat.not_even_iff_odd.mp he)
    have hnE := ha.add hb
    rw [hsum] at hnE
    exact ⟨hnE,⟨fun h ↦ (he h).elim,fun h ↦ ((Nat.not_odd_iff_even.mpr ha) h).elim⟩,
      ⟨fun _ ↦ hb,fun _ ↦ ha⟩⟩

end Erdos583MatchingCutMarkedDevelopment
