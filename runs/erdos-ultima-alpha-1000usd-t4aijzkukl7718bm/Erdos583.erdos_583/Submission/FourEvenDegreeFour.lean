import Submission.FourSpokeLift
import Submission.FourEvenNonclique
import Submission.ThreeEvenDegreeTwo

/-! The four-even case when an even vertex has degree four. -/
namespace Erdos583FourEvenDegreeFourDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails
open Erdos583Work.ComponentDeficit Erdos583Work.BridgeGlue
open Erdos583EvenEdgeRestorationDevelopment Erdos583FourEvenNoncliqueDevelopment
open Erdos583FourSpokeLiftDevelopment Erdos583ThreeEvenDegreeTwoDevelopment
open scoped Classical
set_option maxHeartbeats 2600000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma four_even_clique_degree_four (he : evenCount G=4)
    (hclique : ∀ a b, Even (Nat.card (G.neighborSet a)) →
      Even (Nat.card (G.neighborSet b)) → a ≠ b → G.Adj a b)
    (r : V) (hr : Nat.card (G.neighborSet r)=4) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  have hrE : Even (Nat.card (G.neighborSet r)) := by rw [hr]; decide
  let E := {v | Even (Nat.card (G.neighborSet v))}
  have hdE : (E \ {r}).ncard=3 := by
    have hh := Set.ncard_diff_singleton_add_one (show r ∈ E from hrE)
    change (E \ {r}).ncard+1=evenCount G at hh
    omega
  obtain ⟨a,b,c,hab,hac,hbc,hE⟩ := Set.ncard_eq_three.mp hdE
  have haE : a ∈ E \ {r} := hE.symm ▸ Or.inl rfl
  have hbE : b ∈ E \ {r} := hE.symm ▸ Or.inr (Or.inl rfl)
  have hcE : c ∈ E \ {r} := hE.symm ▸ Or.inr (Or.inr rfl)
  have ha : G.Adj r a := hclique r a hrE haE.1 (Ne.symm (show a ≠ r from haE.2))
  have hb : G.Adj r b := hclique r b hrE hbE.1 (Ne.symm (show b ≠ r from hbE.2))
  have hc : G.Adj r c := hclique r c hrE hcE.1 (Ne.symm (show c ≠ r from hcE.2))
  have hset (v : V) : Even (Nat.card (G.neighborSet v)) ↔ v=r ∨ v=a ∨ v=b ∨ v=c := by
    constructor
    · intro hv
      by_cases hvr : v=r
      · exact Or.inl hvr
      · have hh : v ∈ E \ {r} := ⟨hv,hvr⟩
        rw [hE] at hh
        exact Or.inr hh
    · rintro (rfl|rfl|rfl|rfl)
      · exact hrE
      · exact haE.1
      · exact hbE.1
      · exact hcE.1
  have hNdiff : (G.neighborSet r \ {a,b,c}).ncard=1 := by
    have hsub : ({a,b,c} : Set V) ⊆ G.neighborSet r := by
      rintro v (rfl|rfl|rfl) <;> assumption
    have hh := Set.ncard_diff_add_ncard_of_subset hsub
    have h3 : ({a,b,c} : Set V).ncard=3 := by simp [Set.ncard_insert_of_notMem,hab,hac,hbc]
    rw [h3,show (G.neighborSet r).ncard=4 by simpa only [Nat.card_coe_set_eq] using hr] at hh
    omega
  obtain ⟨x,hxset⟩ := Set.ncard_eq_one.mp hNdiff
  have hxN : x ∈ G.neighborSet r \ {a,b,c} := hxset.symm ▸ rfl
  have hx : G.Adj r x := hxN.1
  have hxa : x ≠ a := fun h ↦ hxN.2 (Or.inl h)
  have hxb : x ≠ b := fun h ↦ hxN.2 (Or.inr (Or.inl h))
  have hxc : x ≠ c := fun h ↦ hxN.2 (Or.inr (Or.inr h))
  have hN (v : V) (hv : G.Adj r v) : v=a ∨ v=b ∨ v=c ∨ v=x := by
    by_cases hm : v ∈ ({a,b,c} : Set V)
    · rcases hm with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · have hh : v ∈ G.neighborSet r \ {a,b,c} := ⟨hv,hm⟩
      rw [hxset] at hh
      exact Or.inr (Or.inr (Or.inr hh))
  let C := G.induce ({r}ᶜ : Set V)
  let a' : ({r}ᶜ : Set V) := ⟨a,ha.ne.symm⟩
  let b' : ({r}ᶜ : Set V) := ⟨b,hb.ne.symm⟩
  let c' : ({r}ᶜ : Set V) := ⟨c,hc.ne.symm⟩
  let x' : ({r}ᶜ : Set V) := ⟨x,hx.ne.symm⟩
  have hxodd : Odd (Nat.card (G.neighborSet x)) := Nat.not_even_iff_odd.mp (by
    rw [hset]
    exact not_or.mpr ⟨hx.ne.symm,not_or.mpr ⟨hxa,not_or.mpr ⟨hxb,hxc⟩⟩⟩)
  have hCx : Even (Nat.card (C.neighborSet x')) := by
    have hh := delete_vertex_adjacent_neighbor_card x' hx.symm
    change Nat.card (C.neighborSet x')+1=Nat.card (G.neighborSet x) at hh
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hxodd
    omega
  have hCo (v : ({r}ᶜ : Set V)) (hvx : v ≠ x') : Odd (Nat.card (C.neighborSet v)) := by
    have hvx' : v.val ≠ x := fun hh ↦ hvx (Subtype.ext hh)
    by_cases hv : G.Adj v.val r
    · have hve : Even (Nat.card (G.neighborSet v.val)) := by
        rw [hset]
        have hh := hN v.val hv.symm
        tauto
      have hh := delete_vertex_adjacent_neighbor_card v hv
      change Nat.card (C.neighborSet v)+1=Nat.card (G.neighborSet v.val) at hh
      rw [Nat.even_iff] at hve
      rw [Nat.odd_iff]
      omega
    · have hh := delete_vertex_nonadjacent_neighbor_card v hv
      rw [show Nat.card (C.neighborSet v)=Nat.card (G.neighborSet v.val) from hh]
      apply Nat.not_even_iff_odd.mp
      rw [hset]
      rintro (h|h|h|h)
      · exact v.property h
      · exact hv (h ▸ ha.symm)
      · exact hv (h ▸ hb.symm)
      · exact hv (h ▸ hc.symm)
  obtain ⟨D,hD,hDn,hDq,hDc⟩ := MarkedBudgets.one_even_path_partition C x' hCx hCo
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hDn
  have hquota (v : ({r}ᶜ : Set V)) : T.quota v=if v=x' then 0 else 1 := by rw [hTq,hDq]; split_ifs <;> rfl
  have hab' : a' ≠ b' := fun h ↦ hab (congrArg Subtype.val h)
  have hac' : a' ≠ c' := fun h ↦ hac (congrArg Subtype.val h)
  have hbc' : b' ≠ c' := fun h ↦ hbc (congrArg Subtype.val h)
  have hax' : a' ≠ x' := fun h ↦ hxa (congrArg Subtype.val h).symm
  have hbx' : b' ≠ x' := fun h ↦ hxb (congrArg Subtype.val h).symm
  have hcx' : c' ≠ x' := fun h ↦ hxc (congrArg Subtype.val h).symm
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := a') (by simp [hquota,hax'])
  obtain ⟨j,hj⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := b') (by simp [hquota,hbx'])
  obtain ⟨l,hl⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := c') (by simp [hquota,hcx'])
  have hsep : i ≠ j ∨ i ≠ l := by
    by_contra hn
    push_neg at hn
    rw [←hn.1] at hj
    rw [←hn.2] at hl
    rcases hi with hi|hi <;> rcases hj with hj|hj <;> rcases hl with hl|hl
    all_goals first | exact hab' (hi.trans hj.symm) | exact hac' (hi.trans hl.symm) | exact hbc' (hj.trans hl.symm)
  have hres : ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card ≤ D.card+1 := by
    rcases hsep with hij|hil
    · exact lift_four_spokes a' b' c' x' hab' hac' hax' hbc' hbx' hcx'
        ha hb hc hx hN T hT i j hij hi hj
    · exact lift_four_spokes a' c' b' x' hac' hab' hax' hbc'.symm hcx' hbx'
        ha hc hb hx (fun v hv ↦ by have hh := hN v hv; tauto) T hT i l hil hi hl
  obtain ⟨F,hF,hFc⟩ := hres
  have hcard : Fintype.card ({r}ᶜ : Set V)+1=Fintype.card V := by
    have hh := Set.ncard_add_ncard_compl ({r} : Set V)
    rw [Set.ncard_singleton,Nat.card_eq_fintype_card] at hh
    simpa only [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Nat.add_comm] using hh
  exact ⟨F,hF,by rw [ceil_half]; omega⟩

lemma four_even_degree_four (he : evenCount G=4) (r : V) (hr : Nat.card (G.neighborSet r)=4) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  by_contra hf
  exact hf (four_even_clique_degree_four he (four_even_failure_clique he hf) r hr)

lemma four_even_failure_even_degree_ge_six (he : evenCount G=4)
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (r : V) (hr : Even (Nat.card (G.neighborSet r))) :
    6 ≤ Nat.card (G.neighborSet r) := by
  let E := {v | Even (Nat.card (G.neighborSet v))}
  have hc := Set.ncard_diff_singleton_add_one (show r ∈ E from hr)
  change (E \ {r}).ncard+1=evenCount G at hc
  have hsub : E \ {r} ⊆ G.neighborSet r := by
    intro v hv
    exact four_even_failure_clique he hf r v hr hv.1 (Ne.symm (show v ≠ r from hv.2))
  have hb := Set.ncard_le_ncard hsub
  have hnot : Nat.card (G.neighborSet r) ≠ 4 := fun h4 ↦ hf (four_even_degree_four he r h4)
  simp only [Nat.card_coe_set_eq,Nat.even_iff] at hr hnot ⊢
  omega

end Erdos583FourEvenDegreeFourDevelopment
