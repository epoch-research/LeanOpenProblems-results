import Submission.Work

/-! Marking obstructions at the first and last cycle visits to any outside
normal group. These are not restricted to neighbors of the root. -/
namespace Erdos583CycleBoundaryMarksDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups Erdos583Work.LollipopEar
open Erdos583Work.CyclePrefixRepair
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma cycle_prefix_not_marked
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (F : Finset (Fin k))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    {z : V} (hz : z ∈ (selectedGraph T F).support)
    (A : G.Walk r z) (B : G.Walk z r) (hform : L.cycle=A.append B)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z) :
    ¬MarkedPartition (selectedGraph T F) F.card z := by
  classical
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hrF := LollipopGroups.outside_support_avoids T r F hav
  have hzr : z ≠ r := by rintro rfl; exact hrF hz
  rintro ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩
  obtain ⟨U,hUs,hrest,_,_,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun j hj ↦ (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      (fun he ↦ hia (he ▸ hj))) D hD hcard
  obtain ⟨j,hj,hUj⟩ := hparts P.toSubgraph hPD
  have hij : L.index ≠ j := fun he ↦ hia (he.symm ▸ hj)
  have hUi := (hrest L.index hia).2.2
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hC : (A.append B).IsCycle := hform ▸ L.isCycle
  have hCS : ∀ y ∈ (A.append B).support, y ∈ L.tail.support → y=r := by
    intro y hy ht
    exact L.inter y (hform.symm ▸ hy) ht
  have hAQ : ∀ y ∈ A.support, y ∈ Q.support → y=z := by
    intro y hy hyQ
    apply hprefix y hy
    apply path_support_subset_graph_support hP hnP y
    simpa only [Q,Walk.support_mapLe_eq_support] using hyQ
  have hmem : (U.walk L.index).toSubgraph=((A.append B).append L.tail).toSubgraph := by
    rw [hUi,L.subgraph,hform]
  have hd : Disjoint ((A.append B).append L.tail).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hmem,←hUj.trans hQe.symm]
    exact U.disjoint hij
  have hcover := cycle_prefix_exchange A B L.tail Q hC hzr L.isPath hQ hCS hAQ hd
  have hnp : ¬(U.walk L.index).IsPath := by
    intro hp
    exact L.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (T.isTrail L.index) hp hUi.symm)
  apply ShortLollipop.maximum_one_defect_no_two_path_cover U (by omega)
    (maximum_of_one_defect_failure hfail U (by omega)) L.index j hij hnp
  rw [hmem,hUj,←hQe]
  exact hcover

lemma outside_group_has_unmarkable_cycle_vertex
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (F : Finset (Fin k))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hhit : ∃ x ∈ L.cycle.support, x ∈ (selectedGraph T F).support) :
    ∃ x ∈ L.cycle.support, x ∈ (selectedGraph T F).support ∧
      ¬MarkedPartition (selectedGraph T F) F.card x := by
  obtain ⟨x,hx,A,B,hform,hA⟩ := QuadrilateralAbsorption.first_hit_split L.cycle (selectedGraph T F).support hhit
  refine ⟨x,?_,hx,cycle_prefix_not_marked hfail T hs r L F hav hx A B hform hA⟩
  rw [hform,Walk.mem_support_append_iff]
  exact Or.inl A.end_mem_support

lemma two_cycle_visits_two_unmarkable
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (F : Finset (Fin k))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hhit : ∃ u v, u ≠ v ∧ u ∈ L.cycle.support ∧ u ∈ (selectedGraph T F).support ∧
      v ∈ L.cycle.support ∧ v ∈ (selectedGraph T F).support) :
    ∃ x y, x ≠ y ∧ x ∈ L.cycle.support ∧ y ∈ L.cycle.support ∧
      x ∈ (selectedGraph T F).support ∧ y ∈ (selectedGraph T F).support ∧
      ¬MarkedPartition (selectedGraph T F) F.card x ∧
      ¬MarkedPartition (selectedGraph T F) F.card y := by
  classical
  obtain ⟨u,v,huv,huC,huF,hvC,hvF⟩ := hhit
  have hrF := LollipopGroups.outside_support_avoids T r F hav
  obtain ⟨x,hx,A,B,hform,hA⟩ := QuadrilateralAbsorption.first_hit_split L.cycle
    (selectedGraph T F).support ⟨u,huC,huF⟩
  have hxr : x ≠ r := by rintro rfl; exact hrF hx
  have hBpath : B.IsPath := (hform ▸ L.isCycle).isPath_of_append_right (Walk.not_nil_of_ne hxr.symm)
  obtain ⟨y,hy,D,E,hB,hE⟩ := CycleDefect.last_hit_split B (selectedGraph T F).support
    ⟨x,B.start_mem_support,hx⟩
  have hxy : x ≠ y := by
    rintro rfl
    have hD : D=Walk.nil := (Walk.isPath_iff_eq_nil _).mp (hB ▸ hBpath).of_append_left
    have hBE : B=E := by simpa only [hD,Walk.nil_append] using hB
    have honly (z : V) (hzC : z ∈ L.cycle.support) (hzF : z ∈ (selectedGraph T F).support) : z=x := by
      rw [hform,Walk.mem_support_append_iff] at hzC
      exact hzC.elim (fun hz ↦ hA z hz hzF) (fun hz ↦ hE z (hBE ▸ hz) hzF)
    exact huv ((honly u huC huF).trans (honly v hvC hvF).symm)
  have hxC : x ∈ L.cycle.support := by
    rw [hform,Walk.mem_support_append_iff]
    exact Or.inl A.end_mem_support
  have hyC : y ∈ L.cycle.support := by
    rw [hform,Walk.mem_support_append_iff]
    apply Or.inr
    rw [hB,Walk.mem_support_append_iff]
    exact Or.inr E.start_mem_support
  let M : RootedCycleRep T r :=
    ⟨L.index,L.finish,L.start_eq,L.finish_eq,L.cycle.reverse,L.tail,L.isCycle.reverse,L.isPath,
      by intro z hz ht; exact L.inter z (by simpa using hz) ht,
      by simpa only [Walk.toSubgraph_append,Walk.toSubgraph_reverse] using L.subgraph⟩
  have hMform : M.cycle=E.reverse.append (A.append D).reverse := by
    simp only [M,hform,hB,Walk.reverse_append,Walk.append_assoc]
  have hEP : ∀ z ∈ E.reverse.support, z ∈ (selectedGraph T F).support → z=y := by
    intro z hz hzF
    exact hE z (by simpa using hz) hzF
  exact ⟨x,y,hxy,hxC,hyC,hx,hy,
    cycle_prefix_not_marked hfail T hs r L F hav hx A B hform hA,
    cycle_prefix_not_marked hfail T hs r M F hav hy E.reverse (A.append D).reverse hMform hEP⟩

lemma two_cycle_visits_two_even_unmarkable
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (F : Finset (Fin k))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hhit : ∃ u v, u ≠ v ∧ u ∈ L.cycle.support ∧ u ∈ (selectedGraph T F).support ∧
      v ∈ L.cycle.support ∧ v ∈ (selectedGraph T F).support) :
    ∃ x y, x ≠ y ∧ x ∈ L.cycle.support ∧ y ∈ L.cycle.support ∧
      x ∈ (selectedGraph T F).support ∧ y ∈ (selectedGraph T F).support ∧
      Even (Nat.card ((selectedGraph T F).neighborSet x)) ∧
      Even (Nat.card ((selectedGraph T F).neighborSet y)) ∧
      ¬MarkedPartition (selectedGraph T F) F.card x ∧
      ¬MarkedPartition (selectedGraph T F) F.card y := by
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hext := normal_group_exact hfail T hs L.index L.member_not_path F hia
  obtain ⟨x,y,hxy,hxC,hyC,hx,hy,hmx,hmy⟩ := two_cycle_visits_two_unmarkable hfail T hs r L F hav hhit
  exact ⟨x,y,hxy,hxC,hyC,hx,hy,CubicRemainder.nonmarked_partition_even hext hmx,
    CubicRemainder.nonmarked_partition_even hext hmy,hmx,hmy⟩

end Erdos583CycleBoundaryMarksDevelopment
