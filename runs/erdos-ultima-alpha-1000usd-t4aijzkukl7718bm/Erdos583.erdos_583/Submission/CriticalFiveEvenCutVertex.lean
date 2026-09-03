import Submission.ThreeEvenCutVertex
import Submission.CriticalFiveEvenClique

/-! Cut constraints at a critical even-even nonedge of a connected five-even
sharp remainder. The endpoints of the critical edge must be separated by any
other even cut vertex. -/
namespace Erdos583CriticalFiveEvenCutVertexDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit Erdos583Work.BridgeGlue
open Erdos583Work.TrailBudget
open Erdos583CriticalEndpointCapacityDevelopment Erdos583CriticalEvenParityDevelopment
open Erdos583ThreeEvenCutVertexDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma delete_connected_of_sup_edge {V : Type*} {H : SimpleGraph V} {a r x : V}
    (har : a ≠ r) (hax : a ≠ x)
    (hc : ((H ⊔ edge r x).induce ({a}ᶜ : Set V)).Connected)
    (hrx : (H.induce ({a}ᶜ : Set V)).Reachable ⟨r,har.symm⟩ ⟨x,hax.symm⟩) :
    (H.induce ({a}ᶜ : Set V)).Connected := by
  let K := H.induce ({a}ᶜ : Set V)
  let J := (H ⊔ edge r x).induce ({a}ᶜ : Set V)
  letI : Nonempty ({a}ᶜ : Set V) := ⟨⟨r,har.symm⟩⟩
  have hl (u v : ({a}ᶜ : Set V)) (h : J.Adj u v) : K.Reachable u v := by
    rcases h with h|h
    · exact (show K.Adj u v from h).reachable
    · rcases ((edge_adj r x u.val v.val).mp h).1 with ⟨hur,hvx⟩|⟨hux,hvr⟩
      · have hu : u=(⟨r,har.symm⟩ : ({a}ᶜ : Set V)) := Subtype.ext hur
        have hv : v=(⟨x,hax.symm⟩ : ({a}ᶜ : Set V)) := Subtype.ext hvx
        simpa only [hu,hv] using hrx
      · have hu : u=(⟨x,hax.symm⟩ : ({a}ᶜ : Set V)) := Subtype.ext hux
        have hv : v=(⟨r,har.symm⟩ : ({a}ᶜ : Set V)) := Subtype.ext hvr
        simpa only [hu,hv] using hrx.symm
  refine ⟨fun u v ↦ ?_⟩
  exact reachable_map_to_reachable id hl (hc.preconnected u v)

variable {V : Type*} [Fintype V] {H : SimpleGraph V} {p : ℕ}

lemma critical_five_even_remaining_noncut_after_add
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (ha : Even (Nat.card (H.neighborSet a))) :
    ((H ⊔ edge r x).induce ({a}ᶜ : Set V)).Connected := by
  by_contra hcut
  have hcount : evenCount (H ⊔ edge r x)=3 := by
    have hh := evenCount_add_even_edge hrx (critical_edge_missing T hp hc) hr hx
    omega
  have ha' : Even (Nat.card ((H ⊔ edge r x).neighborSet a)) := by
    rwa [sup_edge_neighbor_card_of_ne har hax]
  obtain ⟨D,hD,hDc⟩ := sharp_three_even_cut_vertex
    (SimpleGraph.Connected.mono le_sup_left hH) hcount a ha' hcut
  exact hc ⟨D,hD,by omega⟩

lemma critical_five_even_reachable_implies_noncut
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (ha : Even (Nat.card (H.neighborSet a)))
    (hpath : (H.induce ({a}ᶜ : Set V)).Reachable ⟨r,har.symm⟩ ⟨x,hax.symm⟩) :
    (H.induce ({a}ᶜ : Set V)).Connected := by
  exact delete_connected_of_sup_edge har hax
    (critical_five_even_remaining_noncut_after_add T hp hH hn he hrx hr hx hc har hax ha) hpath

lemma critical_five_even_cut_separates
    (T : TrailFamily H p) (hp : ∀ i, (T.walk i).IsPath) (hH : H.Connected)
    (hn : Fintype.card V=2*p+1) (he : evenCount H=5)
    {r x a : V} (hrx : r ≠ x)
    (hr : Even (Nat.card (H.neighborSet r)))
    (hx : Even (Nat.card (H.neighborSet x))) (hc : EdgeCritical H p r x)
    (har : a ≠ r) (hax : a ≠ x) (ha : Even (Nat.card (H.neighborSet a)))
    (hcut : ¬(H.induce ({a}ᶜ : Set V)).Connected) :
    ¬(H.induce ({a}ᶜ : Set V)).Reachable ⟨r,har.symm⟩ ⟨x,hax.symm⟩ := by
  intro hh
  exact hcut (critical_five_even_reachable_implies_noncut T hp hH hn he hrx hr hx hc har hax ha hh)

end Erdos583CriticalFiveEvenCutVertexDevelopment
