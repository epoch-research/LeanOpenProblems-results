import Submission.ThreeEvenSharpRestoration
import Submission.CriticalEvenParity

/-! A critical even-even nonedge at the sharp odd budget restricts the
remaining three even vertices, when there are exactly five in total.
This is a structural restriction, not a contradiction in every case. -/
namespace Erdos583CriticalFiveEvenCoreDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit
open Erdos583ThreeEvenSharpRestorationDevelopment
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

omit [Fintype V] in
lemma add_edge_adj_of_away {r x a b : V} (har : a ≠ r) (hax : a ≠ x) :
    (H ⊔ edge r x).Adj a b ↔ H.Adj a b := by
  simp [sup_adj,edge_adj,har,hax]

lemma critical_five_even_edge_forces_triangle
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a u v : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hur : u ≠ r) (hux : u ≠ x)
    (hvr : v ≠ r) (hvx : v ≠ x) (hau : a ≠ u) (hav : a ≠ v)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hu : Even (Nat.card (H.neighborSet u)))
    (hv : Even (Nat.card (H.neighborSet v))) (huv : H.Adj v u) :
    H.Adj a u ∧ H.Adj a v := by
  have hmiss := critical_edge_missing T hp hc
  have hcount : evenCount (H ⊔ edge r x)=3 := by
    have hh := evenCount_add_even_edge hrx hmiss hr hx
    omega
  have ha' : Even (Nat.card ((H ⊔ edge r x).neighborSet a)) := by
    rwa [sup_edge_neighbor_card_of_ne har hax]
  have hu' : Even (Nat.card ((H ⊔ edge r x).neighborSet u)) := by
    rwa [sup_edge_neighbor_card_of_ne hur hux]
  have hv' : Even (Nat.card ((H ⊔ edge r x).neighborSet v)) := by
    rwa [sup_edge_neighbor_card_of_ne hvr hvx]
  have force (a u v : V) (hau : a ≠ u) (hav : a ≠ v)
      (ha : Even (Nat.card ((H ⊔ edge r x).neighborSet a)))
      (hu : Even (Nat.card ((H ⊔ edge r x).neighborSet u)))
      (hv : Even (Nat.card ((H ⊔ edge r x).neighborSet v)))
      (h : (H ⊔ edge r x).Adj v u) : (H ⊔ edge r x).Adj a u := by
    by_contra hnot
    obtain ⟨D,hD,hDc⟩ := sharp_three_even_edge_nonedge (H ⊔ edge r x)
      hcount a u v hau hav h ha hu hv hnot
    exact hc ⟨D,hD,by omega⟩
  constructor
  · exact (add_edge_adj_of_away har hax).mp
      (force a u v hau hav ha' hu' hv' (Or.inl huv))
  · exact (add_edge_adj_of_away har hax).mp
      (force a v u hav hau ha' hv' hu' (Or.inl huv.symm))

/-- The three even vertices not incident to the critical edge form either
an independent triple or a triangle. -/
lemma critical_five_even_triple_homogeneous
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b c : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hcr : c ≠ r) (hcx : c ≠ x) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hec : Even (Nat.card (H.neighborSet c))) :
    (H.Adj a b ∧ H.Adj a c ∧ H.Adj b c) ∨
      (¬H.Adj a b ∧ ¬H.Adj a c ∧ ¬H.Adj b c) := by
  by_cases hab' : H.Adj a b
  · obtain ⟨hcb,hca⟩ := critical_five_even_edge_forces_triangle T hp hn he
      hrx hr hx hc hcr hcx hbr hbx har hax hbc.symm hac.symm hec hb ha hab'
    exact Or.inl ⟨hab',hca.symm,hcb.symm⟩
  apply Or.inr
  refine ⟨hab',?_,?_⟩
  · intro hac'
    obtain ⟨_,hba⟩ := critical_five_even_edge_forces_triangle T hp hn he
      hrx hr hx hc hbr hbx hcr hcx har hax hbc hab.symm hb hec ha hac'
    exact hab' hba.symm
  · intro hbc'
    obtain ⟨_,hab''⟩ := critical_five_even_edge_forces_triangle T hp hn he
      hrx hr hx hc har hax hcr hcx hbr hbx hac hab ha hec hb hbc'
    exact hab' hab''

/-- A mixed triple away from a critical even-even nonedge forces at least
seven even vertices, rather than merely five. -/
lemma critical_even_edge_mixed_triple_seven_even
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1)
    {r x a u v : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hur : u ≠ r) (hux : u ≠ x)
    (hvr : v ≠ r) (hvx : v ≠ x) (hau : a ≠ u) (hav : a ≠ v)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hu : Even (Nat.card (H.neighborSet u)))
    (hv : Even (Nat.card (H.neighborSet v))) (huv : H.Adj v u) (hnot : ¬H.Adj a u) :
    7 ≤ evenCount H := by
  have hlo := critical_even_edge_five_even T hp hn hrx hr hx hc
  have ho : Odd (evenCount H) := (odd_order_iff_evenCount_odd H).mp ⟨p,hn⟩
  obtain ⟨k,hk⟩ := ho
  by_contra hh
  have he : evenCount H=5 := by omega
  exact hnot (critical_five_even_edge_forces_triangle T hp hn he hrx hr hx hc
    har hax hur hux hvr hvx hau hav ha hu hv huv).1

end Erdos583CriticalFiveEvenCoreDevelopment
