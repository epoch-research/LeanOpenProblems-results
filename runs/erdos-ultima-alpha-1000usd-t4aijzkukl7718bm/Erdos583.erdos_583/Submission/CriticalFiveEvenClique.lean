import Submission.ThreeEvenNontriangle
import Submission.CriticalFiveEvenCore

/-! A critical even-even nonedge at odd order, with exactly five even
vertices, leaves a complete triple of even vertices away from its endpoints. -/
namespace Erdos583CriticalFiveEvenCliqueDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit
open Erdos583ThreeEvenNontriangleDevelopment
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583CriticalFiveEvenCoreDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma critical_five_even_remaining_adj
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (ha : Even (Nat.card (H.neighborSet a))) (hb : Even (Nat.card (H.neighborSet b))) :
    H.Adj a b := by
  by_contra hnot
  have hcount : evenCount (H ⊔ edge r x)=3 := by
    have hh := evenCount_add_even_edge hrx (critical_edge_missing T hp hc) hr hx
    omega
  have ha' : Even (Nat.card ((H ⊔ edge r x).neighborSet a)) := by
    rwa [sup_edge_neighbor_card_of_ne har hax]
  have hb' : Even (Nat.card ((H ⊔ edge r x).neighborSet b)) := by
    rwa [sup_edge_neighbor_card_of_ne hbr hbx]
  obtain ⟨D,hD,hDc⟩ := sharp_three_even_not_clique (H ⊔ edge r x) hcount hab ha' hb'
    (by rwa [add_edge_adj_of_away har hax])
  exact hc ⟨D,hD,by omega⟩

lemma critical_five_even_remaining_triangle
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b c : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hcr : c ≠ r) (hcx : c ≠ x) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (H.neighborSet a))) (hb : Even (Nat.card (H.neighborSet b)))
    (hec : Even (Nat.card (H.neighborSet c))) : H.Adj a b ∧ H.Adj a c ∧ H.Adj b c := by
  exact ⟨critical_five_even_remaining_adj T hp hn he hrx hr hx hc har hax hbr hbx hab ha hb,
    critical_five_even_remaining_adj T hp hn he hrx hr hx hc har hax hcr hcx hac ha hec,
    critical_five_even_remaining_adj T hp hn he hrx hr hx hc hbr hbx hcr hcx hbc hb hec⟩

lemma critical_even_edge_nonadjacent_remaining_seven_even
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1)
    {r x a b : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (ha : Even (Nat.card (H.neighborSet a))) (hb : Even (Nat.card (H.neighborSet b)))
    (hnot : ¬H.Adj a b) : 7 ≤ evenCount H := by
  have hlo := critical_even_edge_five_even T hp hn hrx hr hx hc
  have ho : Odd (evenCount H) := (odd_order_iff_evenCount_odd H).mp ⟨p,hn⟩
  obtain ⟨k,hk⟩ := ho
  by_contra hh
  have he : evenCount H=5 := by omega
  exact hnot (critical_five_even_remaining_adj T hp hn he hrx hr hx hc har hax hbr hbx hab ha hb)

end Erdos583CriticalFiveEvenCliqueDevelopment
