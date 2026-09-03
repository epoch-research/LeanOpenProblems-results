import Submission.Work

/-! Replacing an arbitrary group of members, and the resulting support
expansion inequalities in a smallest-order failure. -/
namespace Erdos583MemberExpansionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.VertexCritical
open Erdos583Work.BridgeGlue Erdos583Work.VertexTracking
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def selectedGraph (T : TrailFamily G k) (A : Finset (Fin k)) : SimpleGraph V where
  Adj x y := ∃ i ∈ A, (T.walk i).toSubgraph.Adj x y
  symm _ _ := by rintro ⟨i,hi,h⟩; exact ⟨i,hi,h.symm⟩
  loopless _ := by rintro ⟨i,_,h⟩; exact h.ne rfl

lemma selectedGraph_le (T : TrailFamily G k) (A : Finset (Fin k)) :
    selectedGraph T A ≤ G := by
  rintro x y ⟨i,_,h⟩
  exact (T.walk i).toSubgraph.adj_sub h

lemma selected_edge_iff (T : TrailFamily G k) (A : Finset (Fin k)) (e : Sym2 V) :
    e ∈ (selectedGraph T A).edgeSet ↔ ∃ i ∈ A, e ∈ (T.walk i).toSubgraph.edgeSet := by
  induction e using Sym2.ind with
  | h x y => rfl

lemma selected_disjoint (T : TrailFamily G k) (A : Finset (Fin k)) (i : Fin k)
    (hi : i ∉ A) : Disjoint (selectedGraph T A).edgeSet (T.walk i).toSubgraph.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj,he⟩ := (selected_edge_iff T A e).mp he
  exact Set.disjoint_left.mp (T.disjoint (show j ≠ i from fun h ↦ hi (h ▸ hj))) he hf

noncomputable def selectedParts (T : TrailFamily G k) (A : Finset (Fin k)) :
    Finset G.Subgraph := A.image (fun i ↦ (T.walk i).toSubgraph)

lemma selectedParts_cover (T : TrailFamily G k) (A : Finset (Fin k)) :
    (⋃ H ∈ selectedParts T A, H.edgeSet)=(selectedGraph T A).edgeSet := by
  classical
  ext e
  simp only [selectedParts,Set.mem_iUnion,Finset.mem_image,selected_edge_iff]
  constructor
  · rintro ⟨H,⟨i,hi,rfl⟩,he⟩
    exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨_,⟨i,hi,rfl⟩,he⟩

lemma selectedParts_pairwise (T : TrailFamily G k) (A : Finset (Fin k)) :
    Set.PairwiseDisjoint (selectedParts T A : Set G.Subgraph) (fun H ↦ H.edgeSet) := by
  classical
  intro H hH J hJ hHJ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hJ
  exact T.disjoint (fun h ↦ hHJ (h ▸ rfl))

lemma selectedParts_paths (T : TrailFamily G k) (A : Finset (Fin k))
    (hp : ∀ i ∈ A, (T.walk i).IsPath) :
    ∀ H ∈ selectedParts T A, IsPathSubgraph H := by
  classical
  intro H hH
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hH
  exact ⟨_,_,_,hp i hi,rfl⟩

/-- A decomposition of any selected edge union may replace that entire
subfamily, while all outside path members are retained. -/
lemma replace_selected (T : TrailFamily G k) (A : Finset (Fin k))
    (hp : ∀ i, i ∉ A → (T.walk i).IsPath)
    (D : Finset (selectedGraph T A).Subgraph)
    (hD : GoodDecomposition (selectedGraph T A) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+(k-A.card) := by
  classical
  let hle := selectedGraph_le T A
  let F := D.image (Subgraph.map (Hom.ofLE hle))
  let B := Finset.univ \ A
  let Q := selectedParts T B
  have hpF : ∀ H ∈ F, IsPathSubgraph H := by
    intro H hH
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    exact lift_path_subgraph hle (hD.1 K hK)
  have hpQ : ∀ H ∈ Q, IsPathSubgraph H :=
    selectedParts_paths T B (fun i hi ↦ hp i (Finset.mem_sdiff.mp hi).2)
  have hcross : ∀ H ∈ F, ∀ J ∈ Q, Disjoint H.edgeSet J.edgeSet := by
    intro H hH J hJ
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hJ
    rw [edgeSet_lift]
    exact (selected_disjoint T A i (Finset.mem_sdiff.mp hi).2).mono_left K.edgeSet_subset
  have hcover : (⋃ H ∈ F, H.edgeSet) ∪ (⋃ H ∈ Q, H.edgeSet)=G.edgeSet := by
    rw [hD.2.lift_union hle,selectedParts_cover]
    ext e
    simp only [Set.mem_union,selected_edge_iff]
    constructor
    · rintro (⟨i,_,hi⟩|⟨i,_,hi⟩) <;> exact (T.cover e).mpr ⟨i,hi⟩
    · intro he
      obtain ⟨i,hi⟩ := (T.cover e).mp he
      by_cases hia : i ∈ A
      · exact Or.inl ⟨i,hia,hi⟩
      · exact Or.inr ⟨i,by simp [B,hia],hi⟩
  obtain ⟨E,hE,hEc⟩ := CutVertexReduction.union_disjoint_partitions F Q hpF hpQ
    (hD.2.lift_pairwise hle) (selectedParts_pairwise T B) hcross hcover
  have hF : F.card ≤ D.card := Finset.card_image_le
  have hQ : Q.card ≤ B.card := Finset.card_image_le
  have hB : B.card=k-A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp
  exact ⟨E,hE,by omega⟩

/-- The original path members in a selected group give a decomposition of
its own edge union with at most the number of selected indices. -/
lemma selected_paths_partition (T : TrailFamily G k) (A : Finset (Fin k))
    (hp : ∀ i ∈ A, (T.walk i).IsPath) :
    ∃ D : Finset (selectedGraph T A).Subgraph, GoodDecomposition (selectedGraph T A) D ∧
      D.card ≤ A.card := by
  classical
  let e := A.equivFin.symm
  have hedge (i : Fin A.card) : ∀ d ∈ (T.walk (e i).val).edges,
      d ∈ (selectedGraph T A).edgeSet := by
    intro d hd
    exact (selected_edge_iff T A d).mpr ⟨(e i).val,(e i).property,
      (T.walk (e i).val).mem_edges_toSubgraph.mpr hd⟩
  let p (i : Fin A.card) := (T.walk (e i).val).transfer (selectedGraph T A) (hedge i)
  have hpe (i : Fin A.card) : (p i).toSubgraph.edgeSet=(T.walk (e i).val).toSubgraph.edgeSet := by
    ext d
    simp only [p,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  let S : TrailFamily (selectedGraph T A) A.card :=
    { start := fun i ↦ T.start (e i).val
      finish := fun i ↦ T.finish (e i).val
      walk := p
      isTrail := fun i ↦ ((hp (e i).val (e i).property).transfer (hedge i)).isTrail
      disjoint := by
        intro i j hij
        rw [hpe,hpe]
        exact T.disjoint (fun h ↦ hij (e.injective (Subtype.ext h)))
      cover := by
        intro d
        simp only [hpe,selected_edge_iff]
        constructor
        · rintro ⟨i,hi,hd⟩
          refine ⟨e.symm ⟨i,hi⟩,?_⟩
          change d ∈ (T.walk (e (e.symm ⟨i,hi⟩)).val).toSubgraph.edgeSet
          rw [e.apply_symm_apply]
          exact hd
        · rintro ⟨i,hi⟩
          exact ⟨(e i).val,(e i).property,hi⟩ }
  exact MatchingAppend.path_family_partition S
    (fun i ↦ (hp (e i).val (e i).property).transfer (hedge i))

lemma selected_support_eq (T : TrailFamily G k) (A : Finset (Fin k))
    (hn : ∀ i ∈ A, ¬(T.walk i).Nil) :
    (selectedGraph T A).support={v | ∃ i ∈ A, v ∈ (T.walk i).support} := by
  ext v
  constructor
  · rintro ⟨w,i,hi,hvw⟩
    exact ⟨i,hi,Walk.mem_support_of_adj_toSubgraph hvw⟩
  · rintro ⟨i,hi,hv⟩
    obtain ⟨w,hw⟩ := walk_vertex_has_subgraph_neighbor (T.walk i) (hn i hi)
      ((T.walk i).mem_verts_toSubgraph.mpr hv)
    exact ⟨w,i,hi,hw⟩

/-- A connected selected union on fewer vertices than a smallest failing
graph must have strictly more than twice as many vertices as selected members,
provided every unselected member is already a path. -/
lemma defect_group_expands {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} {k : ℕ}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (A : Finset (Fin k))
    (hp : ∀ i, i ∉ A → (T.walk i).IsPath)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : (selectedGraph T A).support.ncard < n) :
    2*A.card+1 ≤ (selectedGraph T A).support.ncard := by
  by_contra hn
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall
    (selectedGraph T A) hc hsize
  have hbudget : D.card ≤ A.card := by rw [ceil_half] at hDc; omega
  obtain ⟨E,hE,hEc⟩ := replace_selected T A hp D hD
  exact hfail ⟨E,hE,by have := Finset.card_le_card (Finset.subset_univ A); simp only [Finset.card_univ,Fintype.card_fin] at this; omega⟩

lemma single_defect_group_expands {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} {k : ℕ}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∈ A)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : (selectedGraph T A).support.ncard < n) :
    2*A.card+1 ≤ (selectedGraph T A).support.ncard :=
  defect_group_expands hsmall hfail T A
    (fun j hj ↦ (T.one_defect_other_paths hs i hi).2 j (fun h ↦ hj (h ▸ hia))) hc hsize

lemma selected_reachable (T : TrailFamily G k) (A : Finset (Fin k))
    (i : Fin k) (hi : i ∈ A) {x y : V}
    (hx : x ∈ (T.walk i).support) (hy : y ∈ (T.walk i).support) :
    (selectedGraph T A).Reachable x y := by
  let f : (T.walk i).toSubgraph.coe →g selectedGraph T A :=
    { toFun := Subtype.val, map_rel' := fun h ↦ ⟨i,hi,h⟩ }
  exact ((T.walk i).toSubgraph_connected
    ⟨x,(T.walk i).mem_verts_toSubgraph.mpr hx⟩
    ⟨y,(T.walk i).mem_verts_toSubgraph.mpr hy⟩).map f

lemma selected_connected_of_common_vertex (T : TrailFamily G k) (A : Finset (Fin k))
    (r : V) (hr : ∀ i ∈ A, r ∈ (T.walk i).support) :
    SupportConnected (selectedGraph T A) := by
  rintro x ⟨u,i,hi,hxu⟩ y ⟨v,j,hj,hyv⟩
  exact (selected_reachable T A i hi (Walk.mem_support_of_adj_toSubgraph hxu) (hr i hi)).trans
    (selected_reachable T A j hj (hr j hj) (Walk.mem_support_of_adj_toSubgraph hyv))

/-- The nerve of the family, with adjacency meaning nonempty vertex
intersection. It records connectivity, not edge intersection. -/
def intersectionGraph (T : TrailFamily G k) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ ∃ v, v ∈ (T.walk i).support ∧ v ∈ (T.walk j).support
  symm _ _ := by rintro ⟨h,v,hi,hj⟩; exact ⟨h.symm,v,hj,hi⟩
  loopless _ h := h.1 rfl

lemma selected_connected_of_intersection (T : TrailFamily G k) (A : Finset (Fin k))
    (hc : ((intersectionGraph T).induce (A : Set (Fin k))).Preconnected) :
    SupportConnected (selectedGraph T A) := by
  have link {i j : A} (hij : ((intersectionGraph T).induce (A : Set (Fin k))).Reachable i j) :
      (selectedGraph T A).Reachable (T.start i.val) (T.start j.val) := by
    apply reachable_map_to_reachable (fun i : A ↦ T.start i.val) _ hij
    intro a b hab
    obtain ⟨_,v,hva,hvb⟩ := hab
    exact (selected_reachable T A a.val a.property (T.walk a.val).start_mem_support hva).trans
      (selected_reachable T A b.val b.property hvb (T.walk b.val).start_mem_support)
  rintro x ⟨u,i,hi,hxu⟩ y ⟨v,j,hj,hyv⟩
  exact (selected_reachable T A i hi (Walk.mem_support_of_adj_toSubgraph hxu)
    (T.walk i).start_mem_support).trans ((link (hc ⟨i,hi⟩ ⟨j,hj⟩)).trans
      (selected_reachable T A j hj (T.walk j).start_mem_support
        (Walk.mem_support_of_adj_toSubgraph hyv)))

/-- A connected group of indices containing the single nonpath member must
expand, whenever its edge union is supported on a proper subset of vertices. -/
lemma connected_defect_group_expands {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} {k : ℕ}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∈ A)
    (hc : ((intersectionGraph T).induce (A : Set (Fin k))).Preconnected)
    (hsize : (selectedGraph T A).support.ncard < n) :
    2*A.card+1 ≤ (selectedGraph T A).support.ncard :=
  single_defect_group_expands hsmall hfail T hs i hi A hia
    (selected_connected_of_intersection T A hc) hsize

/-- If deleting one of the path members leaves connected support, at most
one vertex is exclusive to that member. In odd order no vertex is exclusive. -/
lemma deleted_member_support_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hi : ¬(T.walk i).IsPath)
    (j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    (hc : SupportConnected (selectedGraph T (Finset.univ.erase j))) :
    2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1 ≤
      (selectedGraph T (Finset.univ.erase j)).support.ncard := by
  by_cases hsize : (selectedGraph T (Finset.univ.erase j)).support.ncard < n
  · have h := single_defect_group_expands hsmall hfail T hs i hi (Finset.univ.erase j)
      (by simp [hij]) hc hsize
    have hcard := Finset.card_erase_add_one (Finset.mem_univ j)
    rw [Finset.card_univ,Fintype.card_fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊] at hcard
    omega
  · have hh : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by
      rw [ceil_half,Fintype.card_fin]
    omega

lemma odd_deleted_member_spanning {n : ℕ} (hsmall : SmallerOrders n) (ho : Odd n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hi : ¬(T.walk i).IsPath)
    (j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j)
    (hc : SupportConnected (selectedGraph T (Finset.univ.erase j))) :
    (selectedGraph T (Finset.univ.erase j)).support=Set.univ := by
  have hb := deleted_member_support_bound hsmall hfail T hs i hi j hij hc
  obtain ⟨m,hm⟩ := ho
  have hn : n ≤ (selectedGraph T (Finset.univ.erase j)).support.ncard := by
    simp only [Fintype.card_fin,ceil_half] at hb
    omega
  apply (Set.eq_univ_iff_ncard _).mpr
  have hc : (selectedGraph T (Finset.univ.erase j)).support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using Set.ncard_le_card
      (selectedGraph T (Finset.univ.erase j)).support
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using le_antisymm hc hn


end Erdos583MemberExpansionDevelopment
