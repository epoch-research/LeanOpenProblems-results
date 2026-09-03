import Submission.ThreeEvenDegreeTwo

/-! The sharp floor-half path bound when an even cut vertex separates an
all-odd branch from the other even vertices. No unrestricted Gallai bound
or simultaneous endpoint-separation premise is used. -/
namespace Erdos583ThreeEvenCutVertexDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.CutVertexReduction
open Erdos583Work.CutVertexParity Erdos583Work.ComponentDeficit
open Erdos583Work.DoubleEndpointGlue
open Erdos583IndependentTripleSharpDevelopment Erdos583ThreeEvenNontriangleDevelopment
open scoped Classical
set_option maxHeartbeats 2600000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma boundary_neighbor_card (S : Set V) (r : V)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=r)
    (x : S) (hxr : x.val ≠ r) :
    Nat.card ((G.induce S).neighborSet x)=Nat.card (G.neighborSet x.val) := by
  rw [induced_neighbor_card S x.val x.property]
  have hh : G.neighborSet x.val ⊆ S := by
    intro y hy
    by_contra hn
    exact hxr (hcross x.val x.property y hn hy)
  rw [Set.inter_eq_left.mpr hh,Nat.card_coe_set_eq]

lemma evenCount_induce_le_of_boundary (S : Set V) (r : V)
    (hr : Even (Nat.card (G.neighborSet r)))
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=r) :
    evenCount (G.induce S) ≤ evenCount G := by
  let f : {x : S // Even (Nat.card ((G.induce S).neighborSet x))} →
      {x : V // Even (Nat.card (G.neighborSet x))} := fun x ↦ ⟨x.val.val,by
        by_cases hxr : x.val.val=r
        · simpa only [hxr] using hr
        · simpa only [boundary_neighbor_card S r hcross x.val hxr] using x.property⟩
  have hh := Nat.card_le_card_of_injective f (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z ↦ z.val) he)
  simpa only [Nat.card_coe_set_eq,evenCount] using hh

lemma evenCount_induce_le_remove_boundary (S : Set V) (r : V) (hrS : r ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=r)
    (hodd : Odd (Nat.card ((G.induce S).neighborSet ⟨r,hrS⟩))) :
    evenCount (G.induce S) ≤ ({x | Even (Nat.card (G.neighborSet x))} \ {r}).ncard := by
  let f : {x : S // Even (Nat.card ((G.induce S).neighborSet x))} →
      ↥({x | Even (Nat.card (G.neighborSet x))} \ {r}) := fun x ↦ by
    have hxr : x.val.val ≠ r := by
      intro he
      have hx : x.val=(⟨r,hrS⟩ : S) := Subtype.ext he
      exact (Nat.not_even_iff_odd.mpr hodd) (hx ▸ x.property)
    exact ⟨x.val.val,by
      simpa only [boundary_neighbor_card S r hcross x.val hxr] using x.property,hxr⟩
  have hh := Nat.card_le_card_of_injective f (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z ↦ z.val) he)
  simpa only [Nat.card_coe_set_eq,evenCount] using hh

lemma sharp_three_even_boundary (hG : G.Connected) (he : evenCount G=3)
    (S : Set V) (r : V) (hrS : r ∈ S)
    (hr : Even (Nat.card (G.neighborSet r)))
    (hES : {x | Even (Nat.card (G.neighborSet x))} ⊆ S)
    (hproper : ∃ w, w ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=r) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  classical
  let T := insert r Sᶜ
  have hrT : r ∈ T := Or.inl rfl
  have hcrossT := opposite_single_boundary S r hcross
  have hconnS := single_boundary_connected hG S r hrS hcross
  have hconnT := single_boundary_connected hG T r hrT hcrossT
  have hcover := single_boundary_cover S r hcross
  have hinter : S ∩ T ⊆ {r} := by
    rintro x ⟨hx,heq|hn⟩
    · exact heq
    · exact (hn hx).elim
  have hsizeS : 3 ≤ S.ncard := by
    have hh := Set.ncard_le_ncard hES
    change evenCount G ≤ S.ncard at hh
    omega
  have hcardS : Fintype.card S=S.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hcardT : Fintype.card T=T.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hsum : Fintype.card S+Fintype.card T=Fintype.card V+1 := by
    have hh := Set.ncard_add_ncard_compl S
    rw [Nat.card_eq_fintype_card] at hh
    rw [hcardS,hcardT,show T.ncard=Sᶜ.ncard+1 from
      Set.ncard_insert_of_notMem (show r ∉ Sᶜ from not_not.mpr hrS)]
    omega
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w,hw⟩ := hproper
  letI : Nontrivial T := ⟨⟨⟨r,hrT⟩,⟨w,Or.inr hw⟩,by
    intro hh
    have heq : r=w := congrArg Subtype.val hh
    exact hw (heq ▸ hrS)⟩⟩
  have hoddT (x : T) (hxr : x ≠ ⟨r,hrT⟩) :
      Odd (Nat.card ((G.induce T).neighborSet x)) := by
    have hxr' : x.val ≠ r := fun hh ↦ hxr (Subtype.ext hh)
    rw [boundary_neighbor_card T r hcrossT x hxr']
    apply Nat.not_even_iff_odd.mp
    intro hx
    have hxS := hES hx
    rcases x.property with hh|hh
    · exact hxr' hh
    · exact hh hxS
  have hcounts := single_boundary_neighbor_sum (G := G) S r hrS
  have hsmallS : evenCount (G.induce S) ≤ 3 := by
    have hh := evenCount_induce_le_of_boundary S r hr hcross
    omega
  by_cases hTr : Even (Nat.card ((G.induce T).neighborSet ⟨r,hrT⟩))
  · have hSr : Even (Nat.card ((G.induce S).neighborSet ⟨r,hrS⟩)) := by
      rw [Nat.even_iff] at hr hTr ⊢
      change Nat.card ((G.induce S).neighborSet ⟨r,hrS⟩)+
        Nat.card ((G.induce T).neighborSet ⟨r,hrT⟩)=_ at hcounts
      omega
    obtain ⟨E,hE,_,_,hEc⟩ := MarkedBudgets.one_even_path_partition
      (G.induce T) ⟨r,hrT⟩ hTr hoddT
    have hfew : (Finset.univ.filter fun x ↦ Even ((G.induce S).degree x)).card ≤ 3 := by
      rw [evenCount_eq_filter] at hsmallS
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hsmallS
    obtain ⟨D,a,P,hD,hP,hPD,hDc⟩ := MarkedBudgets.few_even_marked
      (G.induce S) hconnS ⟨r,hrS⟩ hfew
    obtain ⟨F,hF,hFc⟩ := glue_induced_even_marked S T r hrS hrT hinter hcover D E hD hE hSr
      ⟨a,P,hP,hPD⟩ (hconnT.preconnected.support_eq_univ.symm ▸ Set.mem_univ _)
    rw [ceil_half] at hDc
    exact ⟨F,hF,by omega⟩
  · have hTro := Nat.not_even_iff_odd.mp hTr
    have hSro : Odd (Nat.card ((G.induce S).neighborSet ⟨r,hrS⟩)) := by
      rw [Nat.even_iff] at hr
      rw [Nat.odd_iff] at hTro ⊢
      change Nat.card ((G.induce S).neighborSet ⟨r,hrS⟩)+
        Nat.card ((G.induce T).neighborSet ⟨r,hrT⟩)=_ at hcounts
      omega
    have hfewS : evenCount (G.induce S) ≤ 2 := by
      have hh := evenCount_induce_le_remove_boundary S r hrS hcross hSro
      have hc := Set.ncard_diff_singleton_add_one (show r ∈ {x | Even (Nat.card (G.neighborSet x))} from hr)
      change _+1=evenCount G at hc
      omega
    have hzeroT : evenCount (G.induce T)=0 := by
      have hh : {x : T | Even (Nat.card ((G.induce T).neighborSet x))}=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        by_cases heq : x=(⟨r,hrT⟩ : T)
        · exact hTr (heq ▸ hx)
        · exact Nat.not_even_iff_odd.mpr (hoddT x heq) hx
      simp only [evenCount,hh,Set.ncard_empty]
    obtain ⟨D,hD,hDc⟩ := sharp_at_most_two_even (G.induce S) hfewS
    obtain ⟨E,hE,hEc⟩ := sharp_at_most_two_even (G.induce T) (by omega)
    have hDS : 0 < endpointMultiplicity D ⟨r,hrS⟩ :=
      ((hD.odd_endpointMultiplicity_iff _).mpr (by
        simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hSro)).pos
    have hET : 0 < endpointMultiplicity E ⟨r,hrT⟩ :=
      ((hE.odd_endpointMultiplicity_iff _).mpr (by
        simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hTro)).pos
    obtain ⟨a,P,hP,hPD⟩ := MarkedBudgets.marked_of_positive_endpoint hD hDS
    obtain ⟨b,Q,hQ,hQE⟩ := MarkedBudgets.marked_of_positive_endpoint hE hET
    obtain ⟨F,hF,hFc⟩ := glue_induced_sides S T r hrS hrT hinter hcover
      D E hD hE P Q hP hQ hPD hQE
    exact ⟨F,hF,by omega⟩

lemma sharp_triangle_even_cut (hG : G.Connected) (he : evenCount G=3)
    (r a b : V) (hra : G.Adj r a) (hab : G.Adj a b) (hbr : b ≠ r)
    (hset : ∀ x, Even (Nat.card (G.neighborSet x)) ↔ x=r ∨ x=a ∨ x=b)
    (hcut : ¬(G.induce ({r}ᶜ : Set V)).Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  classical
  obtain ⟨w,hw,hnon⟩ : ∃ w, G.Adj r w ∧ ¬(within G ({r}ᶜ : Set V)).Reachable a w := by
    by_contra! hh
    exact hcut (DegreeThreeReduction.delete_vertex_connected_of_neighbor_links hG hra hh)
  let S : Set V := {x | x=r ∨ (within G ({r}ᶜ : Set V)).Reachable a x}
  have hrS : r ∈ S := Or.inl rfl
  have haS : a ∈ S := Or.inr Reachable.rfl
  have hbS : b ∈ S := Or.inr (show (within G ({r}ᶜ : Set V)).Adj a b from
    ⟨hab,hra.ne.symm,hbr⟩).reachable
  have hwS : w ∉ S := by
    rintro (hwr|hh)
    · exact hw.ne hwr.symm
    · exact hnon hh
  apply sharp_three_even_boundary hG he S r hrS ((hset r).mpr (Or.inl rfl))
    (by
      intro x hx
      rcases (hset x).mp hx with rfl|rfl|rfl <;> assumption)
    ⟨w,hwS⟩
  intro x hx y hy hxy
  rcases hx with hxr|hh
  · exact hxr
  · by_contra hxr
    have hyr : y ≠ r := fun heq ↦ hy (Or.inl heq)
    exact hy (Or.inr (hh.trans (show (within G ({r}ᶜ : Set V)).Adj x y from
      ⟨hxy,hxr,hyr⟩).reachable))

/-- An even cut vertex is sufficient for the sharp bound with three even
vertices. Unlike the minimum-counterexample cut lemmas, this is unconditional. -/
lemma sharp_three_even_cut_vertex (hG : G.Connected) (he : evenCount G=3)
    (r : V) (hr : Even (Nat.card (G.neighborSet r)))
    (hcut : ¬(G.induce ({r}ᶜ : Set V)).Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+1 ≤ Fintype.card V := by
  let E := {x | Even (Nat.card (G.neighborSet x))}
  have hdiff : (E \ {r}).ncard=2 := by
    have hh := Set.ncard_diff_singleton_add_one (show r ∈ E from hr)
    change (E \ {r}).ncard+1=evenCount G at hh
    omega
  obtain ⟨a,b,hab,hE⟩ := Set.ncard_eq_two.mp hdiff
  have haE : a ∈ E \ {r} := hE.symm ▸ Or.inl rfl
  have hbE : b ∈ E \ {r} := hE.symm ▸ Or.inr rfl
  have hset (x : V) : Even (Nat.card (G.neighborSet x)) ↔ x=r ∨ x=a ∨ x=b := by
    constructor
    · intro hx
      by_cases hxr : x=r
      · exact Or.inl hxr
      · have hh : x ∈ E \ {r} := ⟨hx,hxr⟩
        rw [hE] at hh
        exact Or.inr hh
    · rintro (rfl|rfl|rfl)
      · exact hr
      · exact haE.1
      · exact hbE.1
  by_cases hra : G.Adj r a
  · by_cases habG : G.Adj a b
    · exact sharp_triangle_even_cut hG he r a b hra habG hbE.2 hset hcut
    · exact sharp_three_even_not_clique G he hab haE.1 hbE.1 habG
  · exact sharp_three_even_not_clique G he (Ne.symm (show a ≠ r from haE.2)) hr haE.1 hra

end Erdos583ThreeEvenCutVertexDevelopment
