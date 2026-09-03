import Submission.IndependentTripleCommonNeighbor
import Submission.GuardedPathRestoration

/-! The sharp floor-half bound for graphs whose three even vertices are
independent. Components are handled explicitly. This is not the unrestricted
Gallai path-decomposition conjecture. -/
namespace Erdos583IndependentTripleSharpDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.ComponentDeficit Erdos583Work.ComponentBudget
open Erdos583Work.BridgeGlue
open Erdos583Work.PendantCompletion Erdos583Work.EndpointSelection
open Erdos583IndependentTripleCommonNeighborDevelopment
open Erdos583IndependentThreeEvenSharpDevelopment Erdos583GuardedPathRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2600000
set_option Elab.async false

lemma sharp_independent_three_reachable {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=a ∨ x=b ∨ x=c)
    (hnab : ¬G.Adj a b) (hnac : ¬G.Adj a c) (hnbc : ¬G.Adj b c)
    (hr : G.Reachable a b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  obtain ⟨P,hP,hPl⟩ := hr.exists_path_of_dist
  have hwa : G.Adj P.snd a := (P.adj_snd (Walk.not_nil_of_ne hab)).symm
  by_cases hwc : G.Adj P.snd c
  · by_cases hwb : G.Adj P.snd b
    · exact sharp_independent_three_common_neighbor G a b c P.snd hab hac hbc he
        hwa hwb hwc hnab
    · apply sharp_independent_three_two_neighbors G a c b P.snd hac hab hbc.symm
        (fun x ↦ by rw [he]; tauto) hwa hwc.symm hnac hnab (fun hh ↦ hnbc hh.symm) hwb
  · exact sharp_three_even_guarded_path G a b c hab hac hbc he P hP
      (shortest_path_guard_of_first_nonadjacent P hPl hwc)

lemma sharp_at_most_two_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : evenCount G ≤ 2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  classical
  by_cases ho : Odd (Fintype.card V)
  · have hce := (odd_order_iff_evenCount_odd G).mp ho
    have hc : evenCount G=1 := by rw [Nat.odd_iff] at hce; omega
    obtain ⟨D,hD,hDc⟩ := sharp_one_even_partition G hc
    exact ⟨D,hD,by omega⟩
  · have hev : Fintype.card V%2=0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp ho)
    have hfew : (Finset.univ.filter fun v ↦ Even (G.degree v)).card ≤ 3 := by
      have hh : (Finset.univ.filter fun v ↦ Even (Nat.card (G.neighborSet v))).card ≤ 2 := by
        rw [←evenCount_eq_filter]; exact he
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hh.trans (by omega)
    obtain ⟨D,hD,hDc⟩ := gallai_of_at_most_three_even G hfew
    rw [ceil_half] at hDc
    exact ⟨D,hD,by omega⟩

lemma sharp_connected_independent_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (hthree : evenCount G=3)
    (hind : ∀ u v, Even (Nat.card (G.neighborSet u)) →
      Even (Nat.card (G.neighborSet v)) → ¬G.Adj u v) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  obtain ⟨a,b,c,hab,hac,hbc,hset⟩ := Set.ncard_eq_three.mp hthree
  have he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=a ∨ x=b ∨ x=c :=
    Set.ext_iff.mp hset
  have ha := (he a).mpr (Or.inl rfl)
  have hb := (he b).mpr (Or.inr (Or.inl rfl))
  have hc := (he c).mpr (Or.inr (Or.inr rfl))
  exact sharp_independent_three_reachable G a b c hab hac hbc he
    (hind a b ha hb) (hind a c ha hc) (hind b c hb hc) (hG.preconnected a b)

lemma sharp_independent_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3)
    (hind : ∀ u v, Even (Nat.card (G.neighborSet u)) →
      Even (Nat.card (G.neighborSet v)) → ¬G.Adj u v) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  classical
  have hc (C : G.ConnectedComponent) : evenCount (G.induce C.supp) ≤ 3 := by
    rw [←hthree,component_evenCount_eq]
    exact Set.ncard_le_ncard (fun _ hh ↦ hh.1)
  have hci (C : G.ConnectedComponent) (u v : C.supp)
      (hu : Even (Nat.card ((G.induce C.supp).neighborSet u)))
      (hv : Even (Nat.card ((G.induce C.supp).neighborSet v))) : ¬(G.induce C.supp).Adj u v := by
    rw [component_neighbor_card] at hu hv
    exact hind u.val v.val hu hv
  have hp (C : G.ConnectedComponent) :
      ∃ D : Finset (G.induce C.supp).Subgraph, GoodDecomposition (G.induce C.supp) D ∧
        2*D.card ≤ C.supp.ncard := by
    have hcard : Fintype.card C.supp=C.supp.ncard := by
      rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    by_cases he : evenCount (G.induce C.supp)=3
    · obtain ⟨D,hD,hDc⟩ := sharp_connected_independent_three (G.induce C.supp)
        C.connected_toSimpleGraph he (hci C)
      exact ⟨D,hD,by omega⟩
    · obtain ⟨D,hD,hDc⟩ := sharp_at_most_two_even (G.induce C.supp) (by have := hc C; omega)
      exact ⟨D,hD,by omega⟩
  choose D hD hDc using hp
  obtain ⟨E,hE,hEc⟩ := partition_components G (fun C ↦ (D C).card)
    (fun C ↦ ⟨D C,hD C,le_refl _⟩)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun C _ ↦ hDc C)
  rw [←Finset.mul_sum,sum_component_orders] at hs
  have ho : Odd (Fintype.card V) := (odd_order_iff_evenCount_odd G).mpr (by rw [hthree]; decide)
  rw [Nat.odd_iff] at ho
  exact ⟨E,hE,by omega⟩

end Erdos583IndependentTripleSharpDevelopment
