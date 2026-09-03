import Submission.CriticalFiveEvenCore
import Submission.IndependentThreeEvenSharp
import Submission.GuardedPathRestoration

/-! Common-neighbor and separator restrictions for a critical five-even
remainder whose other three even vertices are independent. -/
namespace Erdos583CriticalFiveEvenNeighborhoodDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583CriticalFiveEvenCoreDevelopment
open Erdos583ThreeEvenSharpRestorationDevelopment
open Erdos583IndependentThreeEvenSharpDevelopment Erdos583GuardedPathRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2600000
set_option Elab.async false
variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma critical_five_even_remaining_set
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (he : evenCount H=5)
    {r x a b c : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hcr : c ≠ r) (hcx : c ≠ x) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hec : Even (Nat.card (H.neighborSet c))) :
    ∀ z, Even (Nat.card ((H ⊔ edge r x).neighborSet z)) ↔ z=a ∨ z=b ∨ z=c := by
  have hcount : evenCount (H ⊔ edge r x)=3 := by
    have hh := evenCount_add_even_edge hrx (critical_edge_missing T hp hc) hr hx
    omega
  have ha' : Even (Nat.card ((H ⊔ edge r x).neighborSet a)) := by
    rwa [sup_edge_neighbor_card_of_ne har hax]
  have hb' : Even (Nat.card ((H ⊔ edge r x).neighborSet b)) := by
    rwa [sup_edge_neighbor_card_of_ne hbr hbx]
  have hc' : Even (Nat.card ((H ⊔ edge r x).neighborSet c)) := by
    rwa [sup_edge_neighbor_card_of_ne hcr hcx]
  exact Set.ext_iff.mp (triple_even_set_of_card_three (H ⊔ edge r x)
    hcount hab hac hbc ha' hb' hc')

omit [Fintype V] in
lemma add_edge_adj_to_away {r x a z : V} (har : a ≠ r) (hax : a ≠ x) :
    (H ⊔ edge r x).Adj z a ↔ H.Adj z a := by
  rw [adj_comm,add_edge_adj_of_away har hax,adj_comm]

/-- Any vertex adjacent to two of the independent remaining even vertices
must also be adjacent to the third. The vertex may be either critical end. -/
lemma critical_five_even_common_neighbor
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b c w : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hcr : c ≠ r) (hcx : c ≠ x) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hec : Even (Nat.card (H.neighborSet c)))
    (hnab : ¬H.Adj a b) (hnac : ¬H.Adj a c) (hnbc : ¬H.Adj b c)
    (hwa : H.Adj w a) (hbw : H.Adj b w) : H.Adj w c := by
  by_contra hnwc
  have hset := critical_five_even_remaining_set T hp he hrx hr hx hc
    har hax hbr hbx hcr hcx hab hac hbc ha hb hec
  obtain ⟨D,hD,hDc⟩ := sharp_independent_three_two_neighbors (H ⊔ edge r x)
    a b c w hab hac hbc hset (Or.inl hwa) (Or.inl hbw)
    (by rwa [add_edge_adj_of_away har hax])
    (by rwa [add_edge_adj_of_away har hax])
    (by rwa [add_edge_adj_of_away hbr hbx])
    (by rwa [add_edge_adj_to_away hcr hcx])
  exact hc ⟨D,hD,by omega⟩

lemma critical_five_even_degree_two_no_pair
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b c w : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hcr : c ≠ r) (hcx : c ≠ x) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hec : Even (Nat.card (H.neighborSet c)))
    (hnab : ¬H.Adj a b) (hnac : ¬H.Adj a c) (hnbc : ¬H.Adj b c)
    (hw : Nat.card (H.neighborSet w) ≤ 2) : ¬(H.Adj w a ∧ H.Adj w b) := by
  rintro ⟨hwa,hwb⟩
  have hwc := critical_five_even_common_neighbor T hp hn he hrx hr hx hc
    har hax hbr hbx hcr hcx hab hac hbc ha hb hec hnab hnac hnbc hwa hwb.symm
  have hsub : ({a,b,c} : Set V) ⊆ H.neighborSet w := by
    rintro z (rfl|rfl|rfl) <;> assumption
  have hh := Set.ncard_le_ncard hsub
  have hcard : ({a,b,c} : Set V).ncard=3 := by
    simp [Set.ncard_insert_of_notMem,hab,hac,hbc]
  rw [hcard] at hh
  rw [Nat.card_coe_set_eq] at hw
  omega

/-- Common neighbors of a and c separate a from b in the remainder. -/
lemma critical_five_even_common_neighbor_separator
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a b c : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (hbr : b ≠ r) (hbx : b ≠ x)
    (hcr : c ≠ r) (hcx : c ≠ x) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (H.neighborSet a)))
    (hb : Even (Nat.card (H.neighborSet b)))
    (hec : Even (Nat.card (H.neighborSet c))) (hnab : ¬H.Adj a b) :
    ¬(H.induce {z | ¬H.Adj z a ∨ ¬H.Adj z c}).Reachable
      ⟨a,Or.inl (H.loopless a)⟩ ⟨b,Or.inl (fun hh ↦ hnab hh.symm)⟩ := by
  intro hreach
  obtain ⟨P,hP,_⟩ := hreach.exists_path_of_dist
  let f : H.induce {z | ¬H.Adj z a ∨ ¬H.Adj z c} →g (H ⊔ edge r x) :=
    { toFun := Subtype.val, map_rel' := fun h ↦ Or.inl h }
  have hset := critical_five_even_remaining_set T hp he hrx hr hx hc
    har hax hbr hbx hcr hcx hab hac hbc ha hb hec
  obtain ⟨D,hD,hDc⟩ := sharp_three_even_guarded_path (H ⊔ edge r x) a b c
    hab hac hbc hset (P.map f) (Walk.map_isPath_of_injective Subtype.val_injective hP) (by
      intro z hz _
      rw [Walk.support_map] at hz
      obtain ⟨y,_,hy⟩ := List.mem_map.mp hz
      have hh : ¬H.Adj z a ∨ ¬H.Adj z c := hy ▸ y.property
      simpa only [add_edge_adj_to_away har hax,add_edge_adj_to_away hcr hcx] using hh)
  exact hc ⟨D,hD,by omega⟩

end Erdos583CriticalFiveEvenNeighborhoodDevelopment
