import Submission.MemberExpansion

/-! Connected groups consisting of paths cannot be compressed by a whole
slot in a smallest-order one-defect failure. -/
namespace Erdos583MemberNormalExpansionDevelopment
open SimpleGraph Erdos583Work Erdos583MemberExpansionDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma one_defect_two_paths [Fintype V] {a b : V} (p : G.Walk a b)
    (hp : p.IsTrail) (hn : ¬p.IsPath) (hc : p.toSubgraph.verts.ncard=p.length) :
    TriangleAbsorption.TwoPathCover (G := G) p.toSubgraph.edgeSet := by
  obtain ⟨x,L,R,hform,hinter⟩ := NilSlot.nonpath_cut p hn
  have hcard := Set.ncard_union_add_ncard_inter L.toSubgraph.verts R.toSubgraph.verts
  have hvl := walk_vertex_ncard_le L
  have hvr := walk_vertex_ncard_le R
  have hu : (L.toSubgraph.verts ∪ R.toSubgraph.verts).ncard=L.length+R.length := by
    simpa only [hform,Walk.toSubgraph_append,Subgraph.verts_sup,Walk.length_append] using hc
  rw [hu] at hcard
  have hL : L.IsPath := (walk_vertex_ncard_eq_iff L).mp (by omega)
  have hR : R.IsPath := (walk_vertex_ncard_eq_iff R).mp (by omega)
  exact ⟨a,x,x,b,L,R,hL,hR,RootedTailSystem.append_trail_disjoint (hform ▸ hp),
    by simp only [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup]⟩

lemma two_path_parts {E : Set (Sym2 V)} (hE : TriangleAbsorption.TwoPathCover (G := G) E) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsPathSubgraph H) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
      (⋃ H ∈ D, H.edgeSet)=E ∧ D.card ≤ 2 := by
  classical
  obtain ⟨a,b,c,d,P,Q,hP,hQ,hd,he⟩ := hE
  refine ⟨{P.toSubgraph,Q.toSubgraph},?_,?_,?_,(Finset.card_insert_le _ _).trans (by simp)⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl|hH
    · exact ⟨a,b,P,hP,rfl⟩
    · have hH := Finset.mem_singleton.mp hH
      subst H
      exact ⟨c,d,Q,hQ,rfl⟩
  · intro H hH J hJ hHJ
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hH hJ
    rcases hH with rfl|rfl <;> rcases hJ with rfl|rfl
    · exact (hHJ rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hHJ rfl).elim
  · simpa only [Finset.mem_insert,Finset.mem_singleton,Set.iUnion_iUnion_eq_or_left,
      Set.iUnion_iUnion_eq_left] using he

/-- Replace one selected group by a path partition and a distinct member by
an arbitrary partial path partition. All remaining path members are retained. -/
lemma replace_selected_and_member (T : TrailFamily G k) (A : Finset (Fin k))
    (i : Fin k) (hi : i ∉ A) (hp : ∀ j, j ∉ A → j ≠ i → (T.walk j).IsPath)
    (D : Finset (selectedGraph T A).Subgraph) (hD : GoodDecomposition (selectedGraph T A) D)
    (R : Finset G.Subgraph) (hpR : ∀ H ∈ R, IsPathSubgraph H)
    (hdR : Set.PairwiseDisjoint (R : Set G.Subgraph) (fun H ↦ H.edgeSet))
    (hcovR : (⋃ H ∈ R, H.edgeSet)=(T.walk i).toSubgraph.edgeSet) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card+1 ≤ D.card+(k-A.card)+R.card := by
  classical
  let hle := selectedGraph_le T A
  let F := D.image (Subgraph.map (Hom.ofLE hle))
  let B := (Finset.univ \ A).erase i
  let Q := selectedParts T B
  let Z := Q ∪ R
  have hRsub (H) (hH : H ∈ R) : H.edgeSet ⊆ (T.walk i).toSubgraph.edgeSet := by
    intro e he
    rw [←hcovR]
    exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,he⟩⟩
  have hB (j : Fin k) (hj : j ∈ B) : j ∉ A ∧ j ≠ i := by
    obtain ⟨hji,hj⟩ := Finset.mem_erase.mp hj
    exact ⟨(Finset.mem_sdiff.mp hj).2,hji⟩
  have hQR : ∀ H ∈ Q, ∀ J ∈ R, Disjoint H.edgeSet J.edgeSet := by
    intro H hH J hJ
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hH
    exact (T.disjoint (hB j hj).2).mono_right (hRsub J hJ)
  have hpQ := selectedParts_paths T B (fun j hj ↦ hp j (hB j hj).1 (hB j hj).2)
  have hpZ : ∀ H ∈ Z, IsPathSubgraph H := by
    intro H hH
    exact (Finset.mem_union.mp hH).elim (hpQ H) (hpR H)
  have hdZ : Set.PairwiseDisjoint (Z : Set G.Subgraph) (fun H ↦ H.edgeSet) := by
    rw [Finset.coe_union]
    exact (selectedParts_pairwise T B).union hdR (fun H hH J hJ _ ↦ hQR H hH J hJ)
  have hpF : ∀ H ∈ F, IsPathSubgraph H := by
    intro H hH
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    exact lift_path_subgraph hle (hD.1 J hJ)
  have hcross : ∀ H ∈ F, ∀ J ∈ Z, Disjoint H.edgeSet J.edgeSet := by
    intro H hH J hJ
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    rw [edgeSet_lift]
    rcases Finset.mem_union.mp hJ with hJ|hJ
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hJ
      exact (selected_disjoint T A j (hB j hj).1).mono_left K.edgeSet_subset
    · exact (selected_disjoint T A i hi).mono K.edgeSet_subset (hRsub J hJ)
  have hcovZ : (⋃ H ∈ Z, H.edgeSet)=(selectedGraph T B).edgeSet ∪ (T.walk i).toSubgraph.edgeSet := by
    simp only [Z,Q,Finset.mem_union,Set.iUnion_or,Set.iUnion_union_distrib,selectedParts_cover,hcovR]
  have hcover : (⋃ H ∈ F, H.edgeSet) ∪ (⋃ H ∈ Z, H.edgeSet)=G.edgeSet := by
    rw [hD.2.lift_union hle,hcovZ]
    ext e
    simp only [Set.mem_union,selected_edge_iff]
    constructor
    · rintro (⟨j,_,hj⟩|⟨j,_,hj⟩|he) <;> first
      | exact (T.cover e).mpr ⟨j,hj⟩
      | exact (T.cover e).mpr ⟨i,he⟩
    · intro he
      obtain ⟨j,hj⟩ := (T.cover e).mp he
      by_cases hja : j ∈ A
      · exact Or.inl ⟨j,hja,hj⟩
      · by_cases hji : j=i
        · subst j; exact Or.inr (Or.inr hj)
        · exact Or.inr (Or.inl ⟨j,by simp [B,hji,hja],hj⟩)
  obtain ⟨E,hE,hEc⟩ := CutVertexReduction.union_disjoint_partitions F Z hpF hpZ
    (hD.2.lift_pairwise hle) hdZ hcross hcover
  have hcF : F.card ≤ D.card := Finset.card_image_le
  have hcQ : Q.card ≤ B.card := Finset.card_image_le
  have hcZ : Z.card ≤ Q.card+R.card := Finset.card_union_le _ _
  have hcB : B.card+1=k-A.card := by
    rw [Finset.card_erase_add_one (by simp [hi]),Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp
  exact ⟨E,hE,by omega⟩

lemma normal_group_cannot_save [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∉ A)
    (D : Finset (selectedGraph T A).Subgraph) (hD : GoodDecomposition (selectedGraph T A) D) :
    A.card ≤ D.card := by
  by_contra hn
  have hc : (T.walk i).toSubgraph.verts.ncard=(T.walk i).length := by
    have hd := (T.one_defect_other_paths hs i hi).1
    have hv := T.defect_add_vertices i
    omega
  obtain ⟨R,hpR,hdR,hcovR,hRc⟩ := two_path_parts (one_defect_two_paths (T.walk i) (T.isTrail i) hi hc)
  obtain ⟨E,hE,hEc⟩ := replace_selected_and_member T A i hia
    (fun j _ hji ↦ (T.one_defect_other_paths hs i hi).2 j hji) D hD R hpR hdR hcovR
  have hcA : A.card ≤ k := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ A))
  exact hfail ⟨E,hE,by omega⟩

/-- Every connected group excluding the one nonpath member has at least
2|A|-1 support vertices. Unlike the defect-group bound, this needs no separate
proper-support assumption: a violating group automatically has smaller order. -/
lemma normal_group_expands {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hi : ¬(T.walk i).IsPath)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A)) :
    2*A.card ≤ (selectedGraph T A).support.ncard+1 := by
  by_contra hn
  have hA : A.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A,fun h ↦ hia (h.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  have hsize : (selectedGraph T A).support.ncard < n := by
    simp only [Fintype.card_fin,ceil_half] at hA
    omega
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall (selectedGraph T A) hc hsize
  have hbound := normal_group_cannot_save hfail T hs i hi A hia D hD
  rw [ceil_half (selectedGraph T A).support.ncard] at hDc
  omega

lemma normal_group_exact [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∉ A) :
    ∃ D : Finset (selectedGraph T A).Subgraph, GoodDecomposition (selectedGraph T A) D ∧
      D.card=A.card ∧ ∀ H ∈ D, H.edgeSet.Nonempty := by
  obtain ⟨D,hD,hDc⟩ := selected_paths_partition T A
    (fun j hj ↦ (T.one_defect_other_paths hs i hi).2 j (fun h ↦ hia (h ▸ hj)))
  have hbound := normal_group_cannot_save hfail T hs i hi A hia D hD
  have heq : D.card=A.card := by omega
  refine ⟨D,hD,heq,?_⟩
  intro H hH
  exact min_decomposition_edgeSet_nonempty hD
    (fun E hE ↦ heq ▸ normal_group_cannot_save hfail T hs i hi A hia E hE) hH

/-- A tight odd-order normal group is not a one-even-vertex graph: the
sharp one-even bound would compress it by one slot and repair the defect. -/
lemma tight_normal_group_three_even [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∉ A)
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1) :
    let J := selectedGraph T A
    3 ≤ ComponentDeficit.evenCount (J.induce J.support) := by
  classical
  let J := selectedGraph T A
  have hcard : Fintype.card J.support=J.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hodd : Odd (Fintype.card J.support) := by
    rw [hcard,Nat.odd_iff]
    change 2*A.card=J.support.ncard+1 at htight
    omega
  have heodd := (ComponentDeficit.odd_order_iff_evenCount_odd (J.induce J.support)).mp hodd
  have hne : ComponentDeficit.evenCount (J.induce J.support) ≠ 1 := by
    intro he
    obtain ⟨D,hD,hDc⟩ := ComponentDeficit.sharp_one_even_partition (J.induce J.support) he
    obtain ⟨E,hE,hEc⟩ := hD.lift_induce_support J
    have hh := normal_group_cannot_save hfail T hs i hi A hia E hE
    rw [hcard] at hDc
    change 2*A.card=J.support.ncard+1 at htight
    omega
  change 3 ≤ ComponentDeficit.evenCount (J.induce J.support)
  obtain ⟨m,hm⟩ := heodd
  omega

/-- Every vertex of a tight odd normal group can be exposed as a genuine
path endpoint without increasing that group's member count. The single-leaf
construction is smaller than the original failing graph. -/
lemma tight_normal_group_marked {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hi : ¬(T.walk i).IsPath)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1)
    (u : Fin n) (hu : u ∈ (selectedGraph T A).support) :
    ∃ D : Finset (selectedGraph T A).Subgraph, ∃ b, ∃ p : (selectedGraph T A).Walk u b,
      GoodDecomposition (selectedGraph T A) D ∧ D.card=A.card ∧
      p.IsPath ∧ ¬p.Nil ∧ p.toSubgraph ∈ D := by
  classical
  let J := selectedGraph T A
  have hcard : Fintype.card J.support=J.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hA : A.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A,fun h ↦ hia (h.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  have hsize : Fintype.card J.support+1 < n := by
    rw [hcard]
    simp only [Fintype.card_fin,ceil_half] at hA
    change 2*A.card=J.support.ncard+1 at htight
    omega
  obtain ⟨D,a,p,hD,hp,hm,hDc⟩ := CutVertexReduction.smaller_order_marked hsmall
    (J.induce J.support) (hc.induce_support ⟨u,hu⟩) ⟨u,hu⟩ hsize
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := MarkedBudgets.lift_induce_marked J.support hD p hp hm
  have hJ : within J J.support=J := by
    ext x y
    exact ⟨fun h ↦ h.1,fun h ↦ ⟨h,J.mem_support.mpr ⟨y,h⟩,J.mem_support.mpr ⟨x,h.symm⟩⟩⟩
  have hresult : ∃ E : Finset J.Subgraph, ∃ q : J.Walk u a.val,
      GoodDecomposition J E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card := by
    have hex : ∃ E : Finset (within J J.support).Subgraph,
        ∃ q : (within J J.support).Walk u a.val,
        GoodDecomposition (within J J.support) E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card :=
      ⟨E,q,hE,hq,hqm,hEc⟩
    exact Eq.mp (congrArg (fun H : SimpleGraph (Fin n) ↦
      ∃ E : Finset H.Subgraph, ∃ q : H.Walk u a.val,
        GoodDecomposition H E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card) hJ) hex
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := hresult
  have hbound := normal_group_cannot_save hfail T hs i hi A hia E hE
  have hbudget : D.card ≤ A.card := by
    rw [hcard,ceil_half (J.support.ncard+1)] at hDc
    change 2*A.card=J.support.ncard+1 at htight
    omega
  have heq : E.card=A.card := by omega
  have hnonempty : q.toSubgraph.edgeSet.Nonempty := min_decomposition_edgeSet_nonempty hE
    (fun F hF ↦ heq ▸ normal_group_cannot_save hfail T hs i hi A hia F hF) hqm
  refine ⟨E,a.val,q,hE,heq,hq,?_,hqm⟩
  intro hn
  obtain ⟨e,he⟩ := hnonempty
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hn,List.not_mem_nil] at he

end Erdos583MemberNormalExpansionDevelopment
