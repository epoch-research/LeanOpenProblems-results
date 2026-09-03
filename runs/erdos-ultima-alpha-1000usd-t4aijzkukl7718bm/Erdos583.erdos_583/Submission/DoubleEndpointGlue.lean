import Submission.Work

/-! Two endpoint joins at a cut vertex, with the saving in path count tracked. -/
open SimpleGraph Erdos583Work
namespace Erdos583DoubleEndpointGlueDevelopment
open Erdos583Work.CutVertexReduction Erdos583Work.MarkedDouble Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

lemma union_partitions_tracked {V : Type*} {G : SimpleGraph V}
    (D E : Finset G.Subgraph)
    (hpD : ∀ H ∈ D, IsPathSubgraph H) (hpE : ∀ H ∈ E, IsPathSubgraph H)
    (hdD : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hdE : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hcross : ∀ H ∈ D, ∀ J ∈ E, Disjoint H.edgeSet J.edgeSet)
    (hcover : (⋃ H ∈ D, H.edgeSet) ∪ (⋃ H ∈ E, H.edgeSet)=G.edgeSet) :
    GoodDecomposition G (D ∪ E) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH|hH
    · exact hpD H hH
    · exact hpE H hH
  · intro H hH J hJ hHJ
    rcases Finset.mem_union.mp hH with hH|hH <;> rcases Finset.mem_union.mp hJ with hJ|hJ
    · exact hdD hH hJ hHJ
    · exact hcross H hH J hJ
    · exact (hcross J hJ H hH).symm
    · exact hdE hH hJ hHJ
  · simpa only [Finset.mem_union,Set.iUnion_or,Set.iUnion_union_distrib] using hcover

lemma merge_two_pairs {V : Type*} {G : SimpleGraph V} {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {K L A B : G.Subgraph}
    (hK : K ∈ D) (hL : L ∈ D) (hA : A ∈ D) (hB : B ∈ D)
    (hKA : K ≠ A) (hLK : L ≠ K) (hLA : L ≠ A)
    (hBK : B ≠ K) (hBA : B ≠ A) (hLB : L ≠ B)
    (hpath₁ : IsPathSubgraph (K ⊔ A)) (hpath₂ : IsPathSubgraph (L ⊔ B)) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+2 ≤ D.card := by
  classical
  let E := insert (K ⊔ A) ((D.erase K).erase A)
  have hE : GoodDecomposition G E := hD.merge hK hA hpath₁
  have hLE : L ∈ E := Finset.mem_insert_of_mem
    (Finset.mem_erase.mpr ⟨hLA,Finset.mem_erase.mpr ⟨hLK,hL⟩⟩)
  have hBE : B ∈ E := Finset.mem_insert_of_mem
    (Finset.mem_erase.mpr ⟨hBA,Finset.mem_erase.mpr ⟨hBK,hB⟩⟩)
  have hEc : E.card+1 ≤ D.card := by
    have hcK := Finset.card_erase_add_one hK
    have hcA := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hKA.symm,hA⟩ : A ∈ D.erase K)
    have hc := Finset.card_insert_le (K ⊔ A) ((D.erase K).erase A)
    dsimp [E]
    omega
  refine ⟨insert (L ⊔ B) ((E.erase L).erase B),hE.merge hLE hBE hpath₂,?_⟩
  have hcL := Finset.card_erase_add_one hLE
  have hcB := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hLB.symm,hBE⟩ : B ∈ E.erase L)
  have hc := Finset.card_insert_le (L ⊔ B) ((E.erase L).erase B)
  omega

lemma two_endpoint_members {V : Type*} {G : SimpleGraph V} {D : Finset G.Subgraph}
    {u : V} (hu : 2 ≤ endpointMultiplicity D u) :
    ∃ K ∈ D, ∃ L ∈ D, K ≠ L ∧ (K.neighborSet u).ncard=1 ∧ (L.neighborSet u).ncard=1 := by
  classical
  obtain ⟨K,hK,L,hL,hKL⟩ := Finset.one_lt_card.mp (show 1 <
    (D.filter fun H ↦ (H.neighborSet u).ncard=1).card by exact lt_of_lt_of_le (by decide) hu)
  exact ⟨K,(Finset.mem_filter.mp hK).1,L,(Finset.mem_filter.mp hL).1,hKL,
    (Finset.mem_filter.mp hK).2,(Finset.mem_filter.mp hL).2⟩

lemma induced_endpoint_union {V : Type*} {G : SimpleGraph V} (S T : Set V) (u : V)
    (huS : u ∈ S) (huT : u ∈ T) (hinter : S ∩ T ⊆ {u})
    {K : (G.induce S).Subgraph} {L : (G.induce T).Subgraph}
    (hK : IsPathSubgraph K) (hL : IsPathSubgraph L)
    (hk : (K.neighborSet ⟨u,huS⟩).ncard=1) (hl : (L.neighborSet ⟨u,huT⟩).ncard=1) :
    IsPathSubgraph (K.map (Embedding.induce S).toHom ⊔ L.map (Embedding.induce T).toHom) := by
  obtain ⟨a,p,hp,rfl⟩ := path_endpoint_of_neighbor_ncard_one hK hk
  obtain ⟨b,q,hq,rfl⟩ := path_endpoint_of_neighbor_ncard_one hL hl
  let p' := p.map (Embedding.induce S).toHom
  let q' := q.map (Embedding.induce T).toHom
  have hpp : p'.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hp
  have hqq : q'.IsPath := Walk.map_isPath_of_injective Subtype.val_injective hq
  refine ⟨a.val,b.val,p'.reverse.append q',?_,by simp [p',q']⟩
  apply path_append_of_support_intersection hpp.reverse hqq
  intro x hx hy
  have hxS : x ∈ S := by
    simp only [p',Walk.support_reverse,List.mem_reverse,Walk.support_map,List.mem_map] at hx
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hxT : x ∈ T := by
    simp only [q',Walk.support_map,List.mem_map] at hy
    obtain ⟨y,_,rfl⟩ := hy
    exact y.property
  exact hinter ⟨hxS,hxT⟩

lemma map_edge_nonempty {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {K : G.Subgraph} (hne : K.edgeSet.Nonempty) :
    (K.map f).edgeSet.Nonempty := by
  rw [Subgraph.edgeSet_map]
  exact hne.image _

lemma ne_of_disjoint_nonempty {V : Type*} {G : SimpleGraph V} {K L : G.Subgraph}
    (hd : Disjoint K.edgeSet L.edgeSet) (hne : K.edgeSet.Nonempty) : K ≠ L := by
  rintro rfl
  obtain ⟨e,he⟩ := hne
  exact Set.disjoint_left.mp hd he he

lemma nonempty_of_endpoint {W : Type*} {J : SimpleGraph W} (C : J.Subgraph) (x : W)
    (hc : (C.neighborSet x).ncard=1) : C.edgeSet.Nonempty := by
  obtain ⟨y,hy⟩ := Set.ncard_eq_one.mp hc
  refine ⟨s(x,y),?_⟩
  change y ∈ C.neighborSet x
  simp [hy]

/-- Two distinct endpoint members on each side allow two independent joins. -/
lemma glue_induced_two_pairs {V : Type*} {G : SimpleGraph V} (S T : Set V) (u : V)
    (huS : u ∈ S) (huT : u ∈ T) (hinter : S ∩ T ⊆ {u})
    (hcover : (within G S).edgeSet ∪ (within G T).edgeSet=G.edgeSet)
    (D : Finset (G.induce S).Subgraph) (E : Finset (G.induce T).Subgraph)
    (hD : GoodDecomposition (G.induce S) D) (hE : GoodDecomposition (G.induce T) E)
    (hDu : 2 ≤ endpointMultiplicity D ⟨u,huS⟩) (hEu : 2 ≤ endpointMultiplicity E ⟨u,huT⟩) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+2 ≤ D.card+E.card := by
  classical
  obtain ⟨K,hK,L,hL,hKL,hKu,hLu⟩ := two_endpoint_members hDu
  obtain ⟨A,hA,B,hB,hAB,hAu,hBu⟩ := two_endpoint_members hEu
  let f : (G.induce S).Subgraph → G.Subgraph := Subgraph.map (Embedding.induce S).toHom
  let g : (G.induce T).Subgraph → G.Subgraph := Subgraph.map (Embedding.induce T).toHom
  let D' := D.image f
  let E' := E.image g
  have hKm : f K ∈ D' := Finset.mem_image_of_mem _ hK
  have hLm : f L ∈ D' := Finset.mem_image_of_mem _ hL
  have hAm : g A ∈ E' := Finset.mem_image_of_mem _ hA
  have hBm : g B ∈ E' := Finset.mem_image_of_mem _ hB
  obtain ⟨hpD,hdD,hcoverD⟩ := partial_induce S D hD
  obtain ⟨hpE,hdE,hcoverE⟩ := partial_induce T E hE
  have hdis := within_edge_disjoint G S T u hinter
  have hcross (H : G.Subgraph) (hH : H ∈ D') (J : G.Subgraph) (hJ : J ∈ E') :
      Disjoint H.edgeSet J.edgeSet := hdis.mono
    (fun _ he ↦ hcoverD ▸ Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,he⟩⟩)
    (fun _ he ↦ hcoverE ▸ Set.mem_iUnion.mpr ⟨J,Set.mem_iUnion.mpr ⟨hJ,he⟩⟩)
  have hF : GoodDecomposition G (D' ∪ E') := union_partitions_tracked D' E' hpD hpE hdD hdE
    hcross (by rw [hcoverD,hcoverE]; exact hcover)
  have hKn := map_edge_nonempty (Embedding.induce S).toHom (nonempty_of_endpoint K (⟨u,huS⟩ : S) hKu)
  have hLn := map_edge_nonempty (Embedding.induce S).toHom (nonempty_of_endpoint L (⟨u,huS⟩ : S) hLu)
  have hAn := map_edge_nonempty (Embedding.induce T).toHom (nonempty_of_endpoint A (⟨u,huT⟩ : T) hAu)
  have hBn := map_edge_nonempty (Embedding.induce T).toHom (nonempty_of_endpoint B (⟨u,huT⟩ : T) hBu)
  have hKL' : f L ≠ f K := by
    apply ne_of_disjoint_nonempty _ hLn
    dsimp [f]
    rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map,Set.disjoint_image_iff
      (Sym2.map.injective (show Function.Injective (Embedding.induce S).toHom from Subtype.val_injective))]
    exact hD.2.1 hL hK hKL.symm
  have hAB' : g B ≠ g A := by
    apply ne_of_disjoint_nonempty _ hBn
    dsimp [g]
    rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map,Set.disjoint_image_iff
      (Sym2.map.injective (show Function.Injective (Embedding.induce T).toHom from Subtype.val_injective))]
    exact hE.2.1 hB hA hAB.symm
  obtain ⟨F,hF,hFc⟩ := merge_two_pairs hF
    (Finset.mem_union_left E' hKm) (Finset.mem_union_left E' hLm)
    (Finset.mem_union_right D' hAm) (Finset.mem_union_right D' hBm)
    (ne_of_disjoint_nonempty (hcross _ hKm _ hAm) hKn) hKL'
    (ne_of_disjoint_nonempty (hcross _ hLm _ hAm) hLn)
    (ne_of_disjoint_nonempty (hcross _ hKm _ hBm).symm hBn) hAB'
    (ne_of_disjoint_nonempty (hcross _ hLm _ hBm) hLn)
    (induced_endpoint_union S T u huS huT hinter (hD.1 K hK) (hE.1 A hA) hKu hAu)
    (induced_endpoint_union S T u huS huT hinter (hD.1 L hL) (hE.1 B hB) hLu hBu)
  have hc := (Finset.card_union_le D' E').trans
    (Nat.add_le_add (Finset.card_image_le (f := f)) (Finset.card_image_le (f := g)))
  exact ⟨F,hF,hFc.trans hc⟩

/-- An even-degree marked side can be glued with a saving of one without
assuming an endpoint in the other side. Empty members are handled by erasure. -/
lemma glue_induced_even_marked {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S T : Set V) (u : V) (huS : u ∈ S) (huT : u ∈ T) (hinter : S ∩ T ⊆ {u})
    (hcover : (within G S).edgeSet ∪ (within G T).edgeSet=G.edgeSet)
    (D : Finset (G.induce S).Subgraph) (E : Finset (G.induce T).Subgraph)
    (hD : GoodDecomposition (G.induce S) D) (hE : GoodDecomposition (G.induce T) E)
    (heven : Even (Nat.card ((G.induce S).neighborSet ⟨u,huS⟩)))
    (hmarked : MarkedAt D ⟨u,huS⟩) (hsupp : (⟨u,huT⟩ : T) ∈ (G.induce T).support) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  classical
  by_cases hnilD : ∃ K ∈ D, K.edgeSet=∅
  · obtain ⟨K,hK,hKe⟩ := hnilD
    obtain ⟨F,hF,hFc⟩ := union_induced_sides S T u hinter hcover (D.erase K) E (hD.erase_empty K hKe) hE
    have hc := Finset.card_erase_add_one hK
    exact ⟨F,hF,by omega⟩
  by_cases hnilE : ∃ K ∈ E, K.edgeSet=∅
  · obtain ⟨K,hK,hKe⟩ := hnilE
    obtain ⟨F,hF,hFc⟩ := union_induced_sides S T u hinter hcover D (E.erase K) hD (hE.erase_empty K hKe)
    have hc := Finset.card_erase_add_one hK
    exact ⟨F,hF,by omega⟩
  have hneD (K) (hK : K ∈ D) : K.edgeSet.Nonempty := Set.nonempty_iff_ne_empty.mpr (fun hh ↦ hnilD ⟨K,hK,hh⟩)
  have hneE (K) (hK : K ∈ E) : K.edgeSet.Nonempty := Set.nonempty_iff_ne_empty.mpr (fun hh ↦ hnilE ⟨K,hK,hh⟩)
  obtain ⟨a,p,hp,hm⟩ := hmarked
  have hpn : ¬p.Nil := by
    intro hn
    cases hn
    simpa using hneD _ hm
  have hpone : (p.toSubgraph.neighborSet ⟨u,huS⟩).ncard=1 := by
    rw [hp.neighborSet_toSubgraph_startpoint hpn]
    simp
  have hpos : 0 < endpointMultiplicity D ⟨u,huS⟩ := Finset.card_pos.mpr
    ⟨p.toSubgraph,Finset.mem_filter.mpr ⟨hm,hpone⟩⟩
  have he : Even (endpointMultiplicity D ⟨u,huS⟩) := by
    apply Nat.not_odd_iff_even.mp
    intro hh
    have ho := (hD.odd_endpointMultiplicity_iff ⟨u,huS⟩).mp hh
    have he' : Even ((G.induce S).degree ⟨u,huS⟩) := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using heven
    exact Nat.not_even_iff_odd.mpr ho he'
  have htwo : 2 ≤ endpointMultiplicity D ⟨u,huS⟩ := by obtain ⟨k,hk⟩ := he; omega
  by_cases hEu : 0 < endpointMultiplicity E ⟨u,huT⟩
  · obtain ⟨b,q,hq,hqm⟩ := MarkedBudgets.marked_of_positive_endpoint hE hEu
    exact glue_induced_sides S T u huS huT hinter hcover D E hD hE p q hp hq hm hqm
  · obtain ⟨E',hE',_,hEc,hE'u,_,_⟩ := EndpointSelection.activate_vertex hE hneE hsupp (by omega)
    obtain ⟨F,hF,hFc⟩ := glue_induced_two_pairs S T u huS huT hinter hcover D E' hD hE' htwo (by omega)
    exact ⟨F,hF,by omega⟩

end Erdos583DoubleEndpointGlueDevelopment
