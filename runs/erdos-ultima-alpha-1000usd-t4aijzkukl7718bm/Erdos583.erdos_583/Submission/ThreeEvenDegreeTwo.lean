import Submission.TwoSpokeSeparatedLift
import Submission.ThreeEvenNontriangle

/-! The sharp floor-half path bound for connected graphs with exactly three
even vertices, one of degree two, apart from the three-vertex triangle. -/
namespace Erdos583ThreeEvenDegreeTwoDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.NormalTrailSystem Erdos583Work.TrailNormalization
open Erdos583Work.ComponentDeficit Erdos583Work.DegreeTwoReduction
open Erdos583AdjacentEndpointUnpairingDevelopment
open Erdos583TwoSpokeSeparatedLiftDevelopment Erdos583ThreeEvenNontriangleDevelopment
open scoped Classical
set_option maxHeartbeats 2600000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma delete_vertex_adjacent_neighbor_card {r : V} (x : ({r}ᶜ : Set V))
    (h : G.Adj x.val r) :
    Nat.card ((G.induce ({r}ᶜ : Set V)).neighborSet x)+1=Nat.card (G.neighborSet x.val) := by
  rw [CutVertexParity.induced_neighbor_card,←Set.diff_eq,Nat.card_coe_set_eq]
  exact Set.ncard_diff_singleton_add_one h

omit [Fintype V] in
lemma delete_vertex_nonadjacent_neighbor_card {r : V} (x : ({r}ᶜ : Set V))
    (h : ¬G.Adj x.val r) :
    Nat.card ((G.induce ({r}ᶜ : Set V)).neighborSet x)=Nat.card (G.neighborSet x.val) := by
  rw [CutVertexParity.induced_neighbor_card,←Set.diff_eq,
    Set.diff_singleton_eq_self (show r ∉ G.neighborSet x.val from h),Nat.card_coe_set_eq]

lemma sharp_triangle_degree_two (hG : G.Connected) (hn : 3 < Fintype.card V)
    (r a b : V) (ha : G.Adj r a) (hb : G.Adj r b) (hab : G.Adj a b)
    (hN : ∀ x, G.Adj r x → x=a ∨ x=b)
    (he : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=r ∨ x=a ∨ x=b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  classical
  let C := G.induce ({r}ᶜ : Set V)
  have hodd (x : ({r}ᶜ : Set V)) : Odd (Nat.card (C.neighborSet x)) := by
    by_cases hxa : x.val=a
    · have hh := delete_vertex_adjacent_neighbor_card x (hxa.symm ▸ ha.symm)
      have he' := (he x.val).mpr (Or.inr (Or.inl hxa))
      rw [Nat.even_iff] at he'
      rw [Nat.odd_iff]
      change Nat.card (C.neighborSet x)+1=Nat.card (G.neighborSet x.val) at hh
      omega
    by_cases hxb : x.val=b
    · have hh := delete_vertex_adjacent_neighbor_card x (hxb.symm ▸ hb.symm)
      have he' := (he x.val).mpr (Or.inr (Or.inr hxb))
      rw [Nat.even_iff] at he'
      rw [Nat.odd_iff]
      change Nat.card (C.neighborSet x)+1=Nat.card (G.neighborSet x.val) at hh
      omega
    · have hnot : ¬G.Adj x.val r := fun h ↦ (hN x.val h.symm).elim hxa hxb
      have hh := delete_vertex_nonadjacent_neighbor_card x hnot
      rw [show Nat.card (C.neighborSet x)=Nat.card (G.neighborSet x.val) from hh]
      apply Nat.not_even_iff_odd.mp
      rw [he]
      exact not_or.mpr ⟨x.property,not_or.mpr ⟨hxa,hxb⟩⟩
  have hC : C.Connected := by
    have hh := bypass_connected hG ha hb hab.ne hN
    rw [bypass_triangle ha hb hab] at hh
    have hEq : (BridgeGlue.within G ({r}ᶜ : Set V)).induce ({r}ᶜ : Set V)=C := by
      ext x y
      exact and_iff_left (And.intro x.property y.property)
    rwa [hEq] at hh
  have hc : Fintype.card ({r}ᶜ : Set V)+1=Fintype.card V := by
    have hh := Set.ncard_add_ncard_compl ({r} : Set V)
    rw [Set.ncard_singleton,Nat.card_eq_fintype_card] at hh
    simpa only [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Nat.add_comm] using hh
  obtain ⟨k,hk,⟨T⟩⟩ := all_odd_normal_trail_system C (by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hodd)
  obtain ⟨R,hR⟩ := T.exists_max_score
  let a' : ({r}ᶜ : Set V) := ⟨a,ha.ne.symm⟩
  let b' : ({r}ᶜ : Set V) := ⟨b,hb.ne.symm⟩
  obtain ⟨S,hS,_,hsep⟩ := separate_distinct_endpoints R (max_score_isPath R hR) hC
    (by omega) a' b' (fun hh ↦ hab.ne (congrArg Subtype.val hh))
  obtain ⟨D,hD,hDc⟩ := lift_two_spokes_separated a' b' ha hb hN S hS hsep
  exact ⟨D,hD,by omega⟩

lemma sharp_three_even_degree_two (hG : G.Connected) (hn : 3 < Fintype.card V)
    (he : evenCount G=3) (r : V) (hr : Nat.card (G.neighborSet r)=2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  have hrE : Even (Nat.card (G.neighborSet r)) := by rw [hr]; decide
  let E := {x | Even (Nat.card (G.neighborSet x))}
  have hdiff : (E \ {r}).ncard=2 := by
    have hh := Set.ncard_diff_singleton_add_one (show r ∈ E from hrE)
    change (E \ {r}).ncard+1=evenCount G at hh
    omega
  obtain ⟨a,b,hab,habE⟩ := Set.ncard_eq_two.mp hdiff
  have haE : a ∈ E \ {r} := habE.symm ▸ Or.inl rfl
  have hbE : b ∈ E \ {r} := habE.symm ▸ Or.inr rfl
  have hset (x : V) : Even (Nat.card (G.neighborSet x)) ↔ x=r ∨ x=a ∨ x=b := by
    constructor
    · intro hx
      by_cases hxr : x=r
      · exact Or.inl hxr
      · have hh : x ∈ E \ {r} := ⟨hx,hxr⟩
        rw [habE] at hh
        exact Or.inr hh
    · rintro (rfl|rfl|rfl)
      · exact hrE
      · exact haE.1
      · exact hbE.1
  by_cases hra : G.Adj r a
  · by_cases hrb : G.Adj r b
    · by_cases habG : G.Adj a b
      · have hNset : G.neighborSet r=({a,b} : Set V) := by
          symm
          apply Set.eq_of_subset_of_ncard_le
          · rintro x (rfl|rfl) <;> assumption
          · rw [←Nat.card_coe_set_eq,hr,Set.ncard_pair hab]
          · exact Set.toFinite _
        exact sharp_triangle_degree_two hG hn r a b hra hrb habG
          (fun x hx ↦ by change x ∈ G.neighborSet r at hx; rwa [hNset] at hx) hset
      · exact sharp_three_even_not_clique G he hab haE.1 hbE.1 habG
    · exact sharp_three_even_not_clique G he (Ne.symm (show b ≠ r from hbE.2)) hrE hbE.1 hrb
  · exact sharp_three_even_not_clique G he (Ne.symm (show a ≠ r from haE.2)) hrE haE.1 hra

end Erdos583ThreeEvenDegreeTwoDevelopment
