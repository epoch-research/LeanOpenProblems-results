import Submission.IndependentSuppression
import Submission.CycleNeighborClosure
import Submission.NormalComponentComplement

/-! Suppressing independent cycle visits repairs a zero-surplus normal component. -/
namespace Erdos583ZeroComponentSuppressionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MemberComponents Erdos583Work.CycleEar Erdos583Work.BridgeGlue
open Erdos583IndependentSuppressionDevelopment Erdos583CycleNeighborClosureDevelopment
open Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000

lemma independent_component_shortcuts {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) (i : Fin k)
    {v : V} (C : G.Walk v v) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmin : ShortestCycle T C.length) (hlen : 4 < C.length)
    (A : (normalGraph T i).ConnectedComponent)
    (hInd : ∀ x ∈ (selectedGraph T (componentMembers T i A)).support,
      ∀ y ∈ (selectedGraph T (componentMembers T i A)).support, ¬C.toSubgraph.Adj x y) :
    let S := (selectedGraph T (componentMembers T i A)).support
    let F := selectedGraph T (Finset.univ \ componentMembers T i A)
    let H := within F Sᶜ
    ∃ R : Finset V, ∃ a b : V → V,
      (R : Set V) ⊆ S ∧
      (∀ r ∈ R, a r ∉ S) ∧ (∀ r ∈ R, b r ∉ S) ∧
      (∀ r ∈ R, a r ≠ b r) ∧ (∀ r ∈ R, ¬H.Adj (a r) (b r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, s(a r,b r)=s(a s,b s) → r=s) ∧ F=H ⊔ spokes R a b := by
  let S := (selectedGraph T (componentMembers T i A)).support
  let F := selectedGraph T (Finset.univ \ componentMembers T i A)
  let H := within F Sᶜ
  let R := (C.toSubgraph.verts ∩ S).toFinset
  have hR (r : V) : r ∈ R ↔ r ∈ C.toSubgraph.verts ∧ r ∈ S := by simp only [R,Set.mem_toFinset,Set.mem_inter_iff]
  have hchoose (r : V) : ∃ a b, r ∈ R → a ≠ b ∧ C.toSubgraph.neighborSet r={a,b} := by
    by_cases hr : r ∈ R
    · obtain ⟨a,b,hab,hN⟩ := Set.ncard_eq_two.mp
        (hC.ncard_neighborSet_toSubgraph_eq_two (C.mem_verts_toSubgraph.mp ((hR r).mp hr).1))
      exact ⟨a,b,fun _ ↦ ⟨hab,hN⟩⟩
    · exact ⟨r,r,fun hh ↦ (hr hh).elim⟩
  choose a b hN using hchoose
  have hna (r : V) (hr : r ∈ R) : C.toSubgraph.Adj r (a r) := by
    change a r ∈ C.toSubgraph.neighborSet r
    rw [(hN r hr).2]
    exact Or.inl rfl
  have hnb (r : V) (hr : r ∈ R) : C.toSubgraph.Adj r (b r) := by
    change b r ∈ C.toSubgraph.neighborSet r
    rw [(hN r hr).2]
    exact Or.inr rfl
  have hAS : (R : Set V) ⊆ S := fun r hr ↦ ((hR r).mp hr).2
  have ha (r : V) (hr : r ∈ R) : a r ∉ S := fun hh ↦ hInd r (hAS hr) (a r) hh (hna r hr)
  have hb (r : V) (hr : r ∈ R) : b r ∉ S := fun hh ↦ hInd r (hAS hr) (b r) hh (hnb r hr)
  have hF (x : V) (hx : x ∈ S) (y : V) : F.Adj x y ↔ C.toSubgraph.Adj x y := by
    rw [complement_adj_at T i A hx,hi]
  have hfresh (r : V) (hr : r ∈ R) : ¬H.Adj (a r) (b r) := by
    intro hh
    obtain ⟨j,hj,hxy⟩ := hh.1
    have hji : j ≠ i := by
      intro he
      have hxyC : C.toSubgraph.Adj (a r) (b r) := by
        subst j
        exact hi ▸ hxy
      have hl := cycle_length_le_three_of_triangle C hC (hna r hr) hxyC (hnb r hr).symm
      omega
    have hrP : r ∉ (T.walk j).support := by
      intro hp
      exact Set.disjoint_left.mp (outside_member_avoids T i A hji (Finset.mem_sdiff.mp hj).2)
        ((T.walk j).mem_verts_toSubgraph.mpr hp) (hAS hr)
    exact shortest_cycle_avoider_no_chord T hs i j hji.symm C hC hi hmin (hna r hr) (hnb r hr)
      (hN r hr).1 hrP ((T.walk j).mem_edges_toSubgraph.mp hxy)
  have hinj (r : V) (hr : r ∈ R) (s : V) (hsR : s ∈ R)
      (he : s(a r,b r)=s(a s,b s)) : r=s := by
    by_contra hrs
    have hsa : C.toSubgraph.Adj s (a r) := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · rw [h1]; exact hna s hsR
      · rw [h1]; exact hnb s hsR
    have hsb : C.toSubgraph.Adj s (b r) := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · rw [h2]; exact hnb s hsR
      · rw [h2]; exact hna s hsR
    have hl := cycle_length_le_four_of_common_neighbors C hC hrs (hN r hr).1
      (hna r hr) (hnb r hr) hsa hsb
    omega
  have hform : F=H ⊔ spokes R a b := by
    ext x y
    constructor
    · intro hxy
      by_cases hx : x ∈ S
      · have hxC := (hF x hx y).mp hxy
        have hxR : x ∈ R := (hR x).mpr ⟨C.toSubgraph.edge_vert hxC,hx⟩
        have hy : y ∈ ({a x,b x} : Set V) := (hN x hxR).2 ▸ hxC
        apply Or.inr
        apply (spokes_adj R a b x y).mpr
        refine ⟨x,hxR,?_⟩
        rcases hy with hy|hy
        · exact Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,hy⟩,hxy.ne⟩)
        · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,hy⟩,hxy.ne⟩)
      · by_cases hy : y ∈ S
        · have hyC := (hF y hy x).mp hxy.symm
          have hyR : y ∈ R := (hR y).mpr ⟨C.toSubgraph.edge_vert hyC,hy⟩
          have hx' : x ∈ ({a y,b y} : Set V) := (hN y hyR).2 ▸ hyC
          apply Or.inr
          apply (spokes_adj R a b x y).mpr
          refine ⟨y,hyR,?_⟩
          rcases hx' with hx'|hx'
          · exact Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨hx',rfl⟩,hxy.ne⟩)
          · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨hx',rfl⟩,hxy.ne⟩)
        · exact Or.inl ⟨hxy,hx,hy⟩
    · rintro (hxy|hxy)
      · exact hxy.1
      · obtain ⟨r,hr,hxy|hxy⟩ := (spokes_adj R a b x y).mp hxy
        · have hh := ((hF r (hAS hr) (a r)).mpr (hna r hr)).symm
          rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · rw [h1,h2]; exact hh
          · rw [h1,h2]; exact hh.symm
        · have hh := (hF r (hAS hr) (b r)).mpr (hnb r hr)
          rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · rw [h1,h2]; exact hh
          · rw [h1,h2]; exact hh.symm
  exact ⟨R,a,b,hAS,ha,hb,fun r hr ↦ (hN r hr).1,hfresh,hinj,hform⟩

section Smallest
open VertexCritical CyclePrefixRepair CycleComponentBudget
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {v : Fin n} (C : G.Walk v v) (hC : C.IsCycle)
  (hi : (T.walk i).toSubgraph=C.toSubgraph) (hmin : ShortestCycle T C.length)
include hsmall hG hfail hs hC hi hmin

lemma shortest_component_positive (A : (normalGraph T i).ConnectedComponent) :
    0 < componentSurplus T i A := by
  let B := componentMembers T i A
  let S := (selectedGraph T B).support
  let F := selectedGraph T (Finset.univ \ B)
  let H := within F Sᶜ
  by_contra hzero
  have hsize : S.ncard ≤ 2*B.card := Nat.sub_eq_zero_iff_le.mp (Nat.eq_zero_of_not_pos hzero)
  have hnp := cycle_member_not_path T i C hC hi
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩
  have hS : S.ncard=2*B.card := le_antisymm hsize (cycle_component_expands hsmall hG hfail T hs hm i C hC hi A)
  have horder : S.ncard < n := FreeTailAbsorption.small_normal_group_proper T i B (removed_not_mem T i A) hsize
  have hInd : ∀ x ∈ S, ∀ y ∈ S, ¬C.toSubgraph.Adj x y := by
    intro x hx y hy
    exact CycleEdgeAbsorption.small_group_cycle_independent hsmall hfail T hs i C hC hi B
      (removed_not_mem T i A) (component_support_connected T i A) horder hsize hx hy
  have hlen := HeptagonExclusion.whole_cycle_length_ge_eight hsmall hG hfail T hs hm i C hC hi
  obtain ⟨R,a,b,hAS,ha,hb,hab,hfresh,hinj,hform⟩ :=
    independent_component_shortcuts T hs i C hC hi hmin (by omega) A hInd
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG i hn A
    exact ⟨x,hx⟩
  have hSum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hSp : 0 < S.ncard := hSn.ncard_pos
  have hFc := complement_connected T hG i hn A
  have hHS : H.support ⊆ Sᶜ := within_support F Sᶜ
  have hex : ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
    obtain ⟨D,hD,hDc⟩ := compressed_partition hsmall R a b H S hAS hHS ha hb hab hfresh hinj
      (hform ▸ hFc) (by omega)
    exact Eq.mp (congrArg (fun J : SimpleGraph (Fin n) ↦ ∃ E : Finset J.Subgraph,
      GoodDecomposition J E ∧ E.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊) hform.symm) ⟨D,hD,hDc⟩
  obtain ⟨D,hD,hDc⟩ := hex
  have hp (j) (hj : j ∉ Finset.univ \ B) : (T.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (T.one_defect_other_paths hs i hnp).2 j ((mem_componentMembers T i j A).mp hjB).1
  obtain ⟨E,hE,hEc⟩ := replace_selected T (Finset.univ \ B) hp D hD
  have hcard : (Finset.univ \ B).card=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hcard] at hEc
  simp only [ceil_half,Fintype.card_fin] at hDc hEc hBc ⊢
  omega

lemma shortest_component_count_le_surplus :
    Nat.card (normalGraph T i).ConnectedComponent ≤ ∑ A, componentSurplus T i A := by
  rw [Nat.card_eq_fintype_card,←Finset.card_univ]
  calc
    _ = ∑ _A : (normalGraph T i).ConnectedComponent, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun A _ ↦ shortest_component_positive hsmall hG hfail T hs i C hC hi hmin A)

lemma shortest_component_count_le_two : Nat.card (normalGraph T i).ConnectedComponent ≤ 2 := by
  have hm := maximum_of_one_defect_failure hfail T hs
  exact (shortest_component_count_le_surplus hsmall hG hfail T hs i C hC hi hmin).trans
    (cycle_surplus_le_two hsmall hG hfail T hs hm i C hC hi)

lemma odd_shortest_component_count_le_one (ho : Odd n) : Nat.card (normalGraph T i).ConnectedComponent ≤ 1 := by
  have hm := maximum_of_one_defect_failure hfail T hs
  exact (shortest_component_count_le_surplus hsmall hG hfail T hs i C hC hi hmin).trans
    (odd_cycle_surplus_le_one hsmall hG hfail T hs hm i C hC hi ho)

lemma odd_shortest_normal_connected (ho : Odd n) :
    SupportConnected (selectedGraph T (Finset.univ.erase i)) := by
  haveI : Subsingleton (normalGraph T i).ConnectedComponent :=
    (Fintype.card_le_one_iff_subsingleton).mp (by simpa only [Nat.card_eq_fintype_card] using odd_shortest_component_count_le_one hsmall hG hfail T hs i C hC hi hmin ho)
  intro x hx y hy
  obtain ⟨u,j,hj,hxj⟩ := hx
  obtain ⟨w,l,hl,hyl⟩ := hy
  let A := (normalGraph T i).connectedComponentMk ⟨j,(Finset.mem_erase.mp hj).1⟩
  have hjA : j ∈ componentMembers T i A := (mem_componentMembers T i j A).mpr ⟨(Finset.mem_erase.mp hj).1,rfl⟩
  have hlA : l ∈ componentMembers T i A := (mem_componentMembers T i l A).mpr
    ⟨(Finset.mem_erase.mp hl).1,Subsingleton.elim _ _⟩
  have hsub : componentMembers T i A ⊆ Finset.univ.erase i := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨((mem_componentMembers T i q A).mp hq).1,Finset.mem_univ _⟩
  exact (component_support_connected T i A x ⟨u,j,hjA,hxj⟩ y ⟨w,l,hlA,hyl⟩).mono
    (CycleGroupDisjoint.selectedGraph_mono T hsub)

lemma odd_shortest_normal_spanning (ho : Odd n) :
    (selectedGraph T (Finset.univ.erase i)).support=Set.univ := by
  have hm := maximum_of_one_defect_failure hfail T hs
  have hn := LowDegreeAdjacency.failure_order_ge_five hG hfail
  have hk : 2 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [ceil_half,Fintype.card_fin]; omega
  haveI : Nontrivial (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j,hji⟩ := exists_ne i
  let A := (normalGraph T i).connectedComponentMk ⟨j,hji⟩
  have hpos := shortest_component_positive hsmall hG hfail T hs i C hC hi hmin A
  have hle : componentSurplus T i A ≤ ∑ B, componentSurplus T i B :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
  have hid := component_surplus_identity T i (cycle_component_expands hsmall hG hfail T hs hm i C hC hi)
  have hb : (selectedGraph T (Finset.univ.erase i)).support.ncard ≤ n := by
    simpa only [Nat.card_fin] using Set.ncard_le_card (selectedGraph T (Finset.univ.erase i)).support
  apply (Set.eq_univ_iff_ncard _).mpr
  simp only [Nat.card_fin]
  simp only [ceil_half,Fintype.card_fin] at hid
  obtain ⟨m,hmo⟩ := ho
  omega

omit hmin in
lemma exists_shortest_connected_spanning_normal (ho : Odd n) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ j r, ∃ D : G.Walk r r,
      U.score=T.score ∧ D.IsCycle ∧ (U.walk j).toSubgraph=D.toSubgraph ∧
      ShortestCycle U D.length ∧
      (∀ A : (normalGraph U j).ConnectedComponent, 0 < componentSurplus U j A) ∧
      SupportConnected (selectedGraph U (Finset.univ.erase j)) ∧
      (selectedGraph U (Finset.univ.erase j)).support=Set.univ := by
  obtain ⟨U,j,r,D,hUs,hD,hj,hshort⟩ := exists_shortest_cycle T i C hC hi
  have hUs' : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by rw [hUs]; exact hs
  exact ⟨U,j,r,D,hUs,hD,hj,hshort,
    shortest_component_positive hsmall hG hfail U hUs' j D hD hj hshort,
    odd_shortest_normal_connected hsmall hG hfail U hUs' j D hD hj hshort ho,
    odd_shortest_normal_spanning hsmall hG hfail U hUs' j D hD hj hshort ho⟩

end Smallest

end Erdos583ZeroComponentSuppressionDevelopment
