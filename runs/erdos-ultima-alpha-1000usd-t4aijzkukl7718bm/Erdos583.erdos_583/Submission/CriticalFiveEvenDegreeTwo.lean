import Submission.CriticalEvenIntersection
import Submission.ThreeEvenDegreeTwo

/-! A degree-two even vertex must meet every critical even-even pair in a
connected five-even sharp remainder. -/
namespace Erdos583CriticalFiveEvenDegreeTwoDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583CriticalEvenIntersectionDevelopment Erdos583ThreeEvenDegreeTwoDevelopment
open Erdos583UnifiedMinimalDefectDevelopment Erdos583NormalRemainderCriticalDevelopment
open Erdos583ShortTailCriticalStarDevelopment Erdos583FixedRemainderEnergyDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false
variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma critical_five_even_remaining_not_degree_two
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) : Nat.card (H.neighborSet a) ≠ 2 := by
  intro ha
  have hcount : evenCount (H ⊔ edge r x)=3 := by
    have hh := evenCount_add_even_edge hrx (critical_edge_missing T hp hc) hr hx
    omega
  have hsize : 5 ≤ Fintype.card V := by
    have hh := Set.ncard_le_card {z | Even (Nat.card (H.neighborSet z))}
    change evenCount H ≤ Nat.card V at hh
    simpa only [he,Nat.card_eq_fintype_card] using hh
  have hdegree : Nat.card ((H ⊔ edge r x).neighborSet a)=2 := by
    rwa [sup_edge_neighbor_card_of_ne har hax]
  obtain ⟨D,hD,hDc⟩ := sharp_three_even_degree_two
    (SimpleGraph.Connected.mono le_sup_left hH) (by omega) hcount a hdegree
  exact hc ⟨D,hD,by omega⟩

lemma critical_five_even_remaining_degree_ge_four
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x)
    (ha : Even (Nat.card (H.neighborSet a))) : 4 ≤ Nat.card (H.neighborSet a) := by
  classical
  letI : Nontrivial V := ⟨⟨r,x,hrx⟩⟩
  have hpos := hH.preconnected.degree_pos_of_nontrivial a
  have hnot := critical_five_even_remaining_not_degree_two T hp hH hn he hrx hr hx hc har hax
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at ha hnot ⊢
  obtain ⟨q,hq⟩ := ha
  omega

lemma degree_two_meets_every_critical_even_edge
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {a r x : V} (ha : Nat.card (H.neighborSet a)=2)
    (hc : (criticalEvenGraph H p).Adj r x) : a=r ∨ a=x := by
  by_contra h
  exact critical_five_even_remaining_not_degree_two T hp hH hn he
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (fun he ↦ h (Or.inl he))
    (fun he ↦ h (Or.inr he)) ha

lemma two_degree_two_critical_edge_unique
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {a b r x : V} (hab : a ≠ b)
    (ha : Nat.card (H.neighborSet a)=2) (hb : Nat.card (H.neighborSet b)=2)
    (hc : (criticalEvenGraph H p).Adj r x) :
    (r=a ∧ x=b) ∨ (r=b ∧ x=a) := by
  have h1 := degree_two_meets_every_critical_even_edge T hp hH hn he ha hc
  have h2 := degree_two_meets_every_critical_even_edge T hp hH hn he hb hc
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2
  · exact (hab (h1.trans h2.symm)).elim
  · exact Or.inl ⟨h1.symm,h2.symm⟩
  · exact Or.inr ⟨h2.symm,h1.symm⟩
  · exact (hab (h1.trans h2.symm)).elim

lemma one_tail_five_even_off_root_degree_ge_four
    (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Odd F.order) (hl : D.rep.tail.length=1)
    (he : evenCount (remainder F D)=5)
    {a : Fin F.order} (har : a ≠ D.root)
    (ha : Even (Nat.card ((remainder F D).neighborSet a)))
    (htwo : ∃ x ∈ ports F D, ∃ y ∈ ports F D, x ≠ y ∧
      Even (Nat.card ((remainder F D).neighborSet x)) ∧
      Even (Nat.card ((remainder F D).neighborSet y))) :
    4 ≤ Nat.card ((remainder F D).neighborSet a) := by
  obtain ⟨T,hT,_⟩ := normal_remainder_energy_optimum F D
  obtain ⟨x,hxp,y,hyp,hxy,hxe,hye⟩ := htwo
  have hr : Even (Nat.card ((remainder F D).neighborSet D.root)) := by
    apply (QuotaParity.quota_even_iff T D.root).mp
    rw [Erdos583UniversalNormalEndpointsDevelopment.short_tail_normal_family_quota_zero F D
      (by omega) T hT]
    exact ⟨0,rfl⟩
  have hsize : Fintype.card (Fin F.order)=2*normalBudget F D+1 := by
    simpa using odd_normalBudget F D ho
  by_cases hax : a=x
  · exact critical_five_even_remaining_degree_ge_four T hT (odd_remainder_connected F D ho)
      (r := D.root) (x := y) (a := a) hsize he
      (fun hh ↦ root_not_ports F D hl (hh.symm ▸ hyp)) hr hye
      (one_tail_ports_critical F D hl y hyp) har (by rwa [hax]) ha
  · exact critical_five_even_remaining_degree_ge_four T hT (odd_remainder_connected F D ho)
      (r := D.root) (x := x) (a := a) hsize he
      (fun hh ↦ root_not_ports F D hl (hh.symm ▸ hxp)) hr hxe
      (one_tail_ports_critical F D hl x hxp) har hax ha

end Erdos583CriticalFiveEvenDegreeTwoDevelopment
