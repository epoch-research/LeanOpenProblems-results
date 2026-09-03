import Submission.Work

/-! Terminal bridge exposure in graphs with exactly one even-degree vertex.
This does not assert the corresponding exposure theorem for nonbridges. -/
namespace Erdos583OneEvenBridgeExposureDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.CutVertexReduction
open Erdos583Work.MarkedBudgets Erdos583Work.CutVertexParity
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma induced_neighbor_card_of_subset {V : Type*} {G : SimpleGraph V}
    (S : Set V) (x : S) (hx : G.neighborSet x.val ⊆ S) :
    Nat.card ((G.induce S).neighborSet x)=Nat.card (G.neighborSet x.val) := by
  rw [induced_neighbor_card S x.val x.property,Set.inter_eq_left.mpr hx,Nat.card_coe_set_eq]

lemma expose_cut_away_from_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V) (hc : Even (Nat.card (G.neighborSet c)))
    (ho : ∀ x, x ≠ c → Odd (Nat.card (G.neighborSet x)))
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S) (hcS : c ∈ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V ∧
      ∃ t, ∃ p : G.Walk u t, (Walk.cons h.symm p).IsPath ∧
        (Walk.cons h.symm p).toSubgraph ∈ D := by
  classical
  let A := insert v S
  let B := Sᶜ
  let cA : A := ⟨c,Or.inr hcS⟩
  let uA : A := ⟨u,Or.inr hu⟩
  let vA : A := ⟨v,Or.inl rfl⟩
  let vB : B := ⟨v,hv⟩
  have hAvu : (G.induce A).Adj uA vA := h
  have hleaf (x : A) (hx : (G.induce A).Adj vA x) : x=uA := by
    rcases x.property with hxv|hxS
    · exact (hx.ne (Subtype.ext hxv).symm).elim
    · exact Subtype.ext (hcross x.val hxS v hv hx.symm).1
  have hAv : Nat.card ((G.induce A).neighborSet vA)=1 := by
    have heq : (G.induce A).neighborSet vA={uA} := by
      ext x
      exact ⟨fun hx ↦ hleaf x hx,fun hx ↦ hx.symm ▸ hAvu.symm⟩
    rw [heq,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hAcard (x : A) (hxS : x.val ∈ S) :
      Nat.card ((G.induce A).neighborSet x)=Nat.card (G.neighborSet x.val) := by
    apply induced_neighbor_card_of_subset
    intro y hxy
    by_cases hy : y ∈ S
    · exact Or.inr hy
    · exact Or.inl (hcross x.val hxS y hy hxy).2
  have hcA : Even (Nat.card ((G.induce A).neighborSet cA)) := by
    rw [hAcard cA hcS]; exact hc
  have hoA (x : A) (hx : x ≠ cA) : Odd (Nat.card ((G.induce A).neighborSet x)) := by
    rcases x.property with hxv|hxS
    · have he : x=vA := Subtype.ext hxv
      rw [he,hAv]; exact odd_one
    · rw [hAcard x hxS]
      exact ho x.val (fun he ↦ hx (Subtype.ext he))
  have hBcard (x : B) (hxv : x ≠ vB) :
      Nat.card ((G.induce B).neighborSet x)=Nat.card (G.neighborSet x.val) := by
    apply induced_neighbor_card_of_subset
    intro y hxy hy
    have he := (hcross y hy x.val x.property hxy.symm).2
    exact hxv (Subtype.ext he)
  have hBv : Nat.card ((G.induce B).neighborSet vB)+1=Nat.card (G.neighborSet v) := by
    rw [induced_neighbor_card B v hv]
    have heq : G.neighborSet v ∩ B=G.neighborSet v \ {u} := by
      ext x
      constructor
      · rintro ⟨hvx,hx⟩
        exact ⟨hvx,fun he ↦ hx (he.symm ▸ hu)⟩
      · rintro ⟨hvx,hxu⟩
        refine ⟨hvx,?_⟩
        intro hxS
        exact hxu (hcross x hxS v hv hvx.symm).1
    rw [heq,Nat.card_coe_set_eq]
    exact Set.ncard_diff_singleton_add_one h.symm
  have hvB : Even (Nat.card ((G.induce B).neighborSet vB)) := by
    have hvodd := ho v (fun he ↦ hv (he.symm ▸ hcS))
    rw [←hBv,Nat.odd_add_one] at hvodd
    exact Nat.not_odd_iff_even.mp hvodd
  have hoB (x : B) (hx : x ≠ vB) : Odd (Nat.card ((G.induce B).neighborSet x)) := by
    rw [hBcard x hx]
    exact ho x.val (fun he ↦ x.property (he.symm ▸ hcS))
  obtain ⟨D,hD,_,_,hDc⟩ := one_even_path_partition (G.induce A) cA hcA hoA
  obtain ⟨E,hE,_,_,hEc⟩ := one_even_path_partition (G.induce B) vB hvB hoB
  obtain ⟨hDp,hDd,hDcover⟩ := partial_induce A D hD
  obtain ⟨hEp,hEd,hEcover⟩ := partial_induce B E hE
  let D' := D.image (Subgraph.map (Embedding.induce A).toHom)
  let E' := E.image (Subgraph.map (Embedding.induce B).toHom)
  have hinter : A ∩ B ⊆ {v} := by
    intro x hx
    exact hx.1.resolve_right hx.2
  have hdis := within_edge_disjoint G A B v hinter
  have hsep (K : G.Subgraph) (hK : K ∈ D') (L : G.Subgraph) (hL : L ∈ E') :
      Disjoint K.edgeSet L.edgeSet := hdis.mono
    (fun _ he ↦ hDcover ▸ Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,he⟩⟩)
    (fun _ he ↦ hEcover ▸ Set.mem_iUnion.mpr ⟨L,Set.mem_iUnion.mpr ⟨hL,he⟩⟩)
  have hcover : (within G A).edgeSet ∪ (within G B).edgeSet=G.edgeSet := by
    ext e
    constructor
    · rintro (he|he)
      · exact edgeSet_mono (within_le _ _) he
      · exact edgeSet_mono (within_le _ _) he
    · induction e using Sym2.ind with
      | h x y =>
        intro he
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · exact Or.inl ⟨he,Or.inr hx,Or.inr hy⟩
        · obtain ⟨rfl,rfl⟩ := hcross x hx y hy he
          exact Or.inl ⟨he,Or.inr hu,Or.inl rfl⟩
        · obtain ⟨rfl,rfl⟩ := hcross y hy x hx he.symm
          exact Or.inl ⟨he,Or.inl rfl,Or.inr hu⟩
        · exact Or.inr ⟨he,hx,hy⟩
  have hF : GoodDecomposition G (D' ∪ E') :=
    DoubleEndpointGlue.union_partitions_tracked D' E' hDp hEp hDd hEd hsep
      (by rw [hDcover,hEcover]; exact hcover)
  have hbound : 2*(D' ∪ E').card+1 ≤ Fintype.card V := by
    have hsum : A.ncard+B.ncard=Fintype.card V+1 := by
      rw [Set.ncard_insert_of_notMem hv]
      have hh := S.ncard_add_ncard_compl
      rw [Nat.card_eq_fintype_card] at hh
      dsimp only [B]
      omega
    have hcA' : Fintype.card A=A.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    have hcB' : Fintype.card B=B.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rw [hcA'] at hDc
    rw [hcB'] at hEc
    have hdi : D'.card ≤ D.card := Finset.card_image_le
    have hei : E'.card ≤ E.card := Finset.card_image_le
    have hf := Finset.card_union_le D' E'
    omega
  have heD : ∃ K ∈ D, s(uA,vA) ∈ K.edgeSet := by
    have hh : s(uA,vA) ∈ ⋃ K ∈ D, K.edgeSet := hD.2.2.symm ▸ hAvu
    simpa only [Set.mem_iUnion,exists_prop] using hh
  obtain ⟨K,hKD,hKe⟩ := heD
  obtain ⟨a,p,hp,hKp⟩ := terminal_edge_rep hAvu hleaf (hD.1 K hKD) hKe
  let q : G.Walk u a.val := p.map (Embedding.induce A).toHom
  have hq : (Walk.cons h.symm q).IsPath := by
    simpa only [Walk.map_cons] using Walk.map_isPath_of_injective
      (f := (Embedding.induce A).toHom) Subtype.val_injective hp
  refine ⟨D' ∪ E',hF,hbound,a.val,q,hq,Finset.mem_union_left _ ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨K,hKD,?_⟩
  rw [hKp,←Walk.toSubgraph_map]
  rfl


lemma one_even_card_eq_of_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V) (hc : Even (Nat.card (G.neighborSet c)))
    (ho : ∀ x, x ≠ c → Odd (Nat.card (G.neighborSet x)))
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hb : 2*D.card+1 ≤ Fintype.card V) : 2*D.card+1=Fintype.card V := by
  classical
  have hpar (x : V) : Odd (G.degree x) ↔ x ≠ c := by
    have hc' : Even (G.degree c) := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hc
    constructor
    · intro hx he
      exact (Nat.not_odd_iff_even.mpr hc') (he ▸ hx)
    · intro hx
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho x hx
  have hcount : Fintype.card {x : V // Odd (G.degree x)}=Fintype.card V-1 := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hpar),Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have hlow := odd_vertices_le_twice_path_count G hD
  rw [hcount] at hlow
  omega

/-- A bridge always has a terminal occurrence in a sharp one-even-vertex
partition. The end can be chosen on the side away from the unique even vertex;
no assertion is made for arbitrary prescribed orientations or nonbridges. -/
lemma one_even_bridge_exposure {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V) (hc : Even (Nat.card (G.neighborSet c)))
    (ho : ∀ x, x ≠ c → Odd (Nat.card (G.neighborSet x)))
    {u v : V} (h : G.Adj u v) (hb : G.IsBridge s(u,v)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1=Fintype.card V ∧
      ((∃ t, ∃ p : G.Walk u t, (Walk.cons h.symm p).IsPath ∧
        (Walk.cons h.symm p).toSubgraph ∈ D) ∨
       (∃ t, ∃ p : G.Walk v t, (Walk.cons h p).IsPath ∧
        (Walk.cons h p).toSubgraph ∈ D)) := by
  classical
  obtain ⟨S,hu,hv,hcross⟩ := bridge_cut hb
  by_cases hcS : c ∈ S
  · obtain ⟨D,hD,hDc,ht⟩ := expose_cut_away_from_even G c hc ho S h hu hv hcS hcross
    exact ⟨D,hD,one_even_card_eq_of_bound G c hc ho hD hDc,Or.inl ht⟩
  · have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
      intro x hx y hy hxy
      have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
      exact (hcross y hyS x hx hxy.symm).symm
    obtain ⟨D,hD,hDc,ht⟩ := expose_cut_away_from_even G c hc ho Sᶜ h.symm hv
      (not_not.mpr hu) hcS hcross'
    exact ⟨D,hD,one_even_card_eq_of_bound G c hc ho hD hDc,Or.inr ht⟩

end Erdos583OneEvenBridgeExposureDevelopment
