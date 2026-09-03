import Submission.Work

/-! Marked outside groups cannot cut a short whole cycle into two carriers. -/
namespace Erdos583CarrierCutsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

omit [Fintype V] in
lemma cut_carrier_at_marked_path (T : TrailFamily G k) (j m : Fin k) (hjm : j ≠ m)
    {a z b d : V} (A : G.Walk a z) (B : G.Walk z b) (Q : G.Walk z d)
    (hAB : (A.append B).IsPath) (hQ : Q.IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hm : (T.walk m).toSubgraph=Q.toSubgraph)
    (hAQ : ∀ x ∈ A.support, x ∈ Q.support → x=z) :
    ∃ U : TrailFamily G k, U.score=T.score ∧
      (U.walk j).toSubgraph=B.toSubgraph ∧ (U.walk m).toSubgraph=(A.append Q).toSubgraph ∧
      (∀ l, l ≠ j → l ≠ m → (U.walk l).toSubgraph=(T.walk l).toSubgraph) := by
  have hA := hAB.of_append_left
  have hB := hAB.of_append_right
  have hX := path_append_of_support_intersection hA hQ hAQ
  have hdOld : Disjoint (A.append B).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hj,←hm]
    exact T.disjoint hjm
  have hd : Disjoint B.toSubgraph.edgeSet (A.append Q).toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    apply disjoint_sup_right.mpr
    refine ⟨(RootedTailSystem.append_trail_disjoint hAB.isTrail).symm,?_⟩
    exact hdOld.mono_left (by simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]; exact Set.subset_union_right)
  have he : B.toSubgraph.edgeSet ∪ (A.append Q).toSubgraph.edgeSet =
      (T.walk j).toSubgraph.edgeSet ∪ (T.walk m).toSubgraph.edgeSet := by
    rw [hj,hm]
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ext e
    simp only [Set.mem_union]
    tauto
  obtain ⟨U,hUj,hUm,hrest,hUs⟩ := GeneralPair.replace_two T j m hjm z b a d B (A.append Q)
    hB.isTrail hX.isTrail hd he
  rw [hj,hm,(walk_vertex_ncard_eq_iff _).mpr hAB,(walk_vertex_ncard_eq_iff _).mpr hQ,
    (walk_vertex_ncard_eq_iff _).mpr hB,(walk_vertex_ncard_eq_iff _).mpr hX] at hUs
  simp only [Walk.length_append] at hUs
  exact ⟨U,by omega,hUj,hUm,hrest⟩

lemma marked_group_cut_intersections
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z) :
    ((C.toSubgraph.verts ∩ A.toSubgraph.verts).Nonempty →
      5 ≤ (C.toSubgraph.verts ∩ A.toSubgraph.verts).ncard) ∧
    ((C.toSubgraph.verts ∩ B.toSubgraph.verts).Nonempty →
      5 ≤ (C.toSubgraph.verts ∩ B.toSubgraph.verts).ncard) := by
  classical
  have hnp := CycleEar.cycle_member_not_path T i C hC hi
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark
  obtain ⟨Z,hZs,hrest,_,_,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun l hl ↦ (T.one_defect_other_paths hs i hnp).2 l (fun he ↦ hiF (he ▸ hl))) D hD hcard
  obtain ⟨m,hmF,hZm⟩ := hparts P.toSubgraph hPD
  have hjm : j ≠ m := fun he ↦ hjF (he.symm ▸ hmF)
  have him : i ≠ m := fun he ↦ hiF (he.symm ▸ hmF)
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hQs (x : V) (hx : x ∈ Q.support) : x ∈ (selectedGraph T F).support := by
    apply path_support_subset_graph_support hP hnP x
    simpa only [Q,Walk.support_mapLe_eq_support] using hx
  have hAQ : ∀ x ∈ A.support, x ∈ Q.support → x=z := fun x hx hy ↦ hprefix x hx (hQs x hy)
  obtain ⟨U,hUs,hUj,hUm,hUrest⟩ := cut_carrier_at_marked_path Z j m hjm A B Q hAB hQ
    ((hrest j hjF).2.2.trans hj) (hZm.trans hQe.symm) hAQ
  have hscore : U.score+1=G.edgeSet.ncard+k := by omega
  have hmax := CyclePrefixRepair.maximum_of_one_defect_failure hfail U hscore
  have hUi : (U.walk i).toSubgraph=C.toSubgraph := (hUrest i hij him).trans ((hrest i hiF).2.2.trans hi)
  have hX := path_append_of_support_intersection hAB.of_append_left hQ hAQ
  have hUpm : (U.walk m).IsPath := ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail m) hX hUm
  have hUpj : (U.walk j).IsPath := ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail j) hAB.of_append_right hUj
  have hinter : C.toSubgraph.verts ∩ (A.append Q).toSubgraph.verts =
      C.toSubgraph.verts ∩ A.toSubgraph.verts := by
    rw [Walk.toSubgraph_append,Subgraph.verts_sup]
    ext x
    constructor
    · rintro ⟨hx,hA|hQ⟩
      · exact ⟨hx,hA⟩
      · exact (hFC x (hQs x (Q.mem_verts_toSubgraph.mp hQ)) (C.mem_verts_toSubgraph.mp hx)).elim
    · rintro ⟨hx,hA⟩
      exact ⟨hx,Or.inl hA⟩
  constructor
  · rintro ⟨x,hxC,hxA⟩
    have hh := CycleIntersectionBound.maximal_cycle_intersection_ge_five U hmax i m him C hC hUi hUpm
      ⟨x,by rw [←Walk.mem_verts_toSubgraph,hUm,Walk.toSubgraph_append,Subgraph.verts_sup]; exact Or.inl hxA,
        C.mem_verts_toSubgraph.mp hxC⟩
    rwa [hUm,hinter] at hh
  · rintro ⟨x,hxC,hxB⟩
    have hh := CycleIntersectionBound.maximal_cycle_intersection_ge_five U hmax i j hij C hC hUi hUpj
      ⟨x,by rwa [←Walk.mem_verts_toSubgraph,hUj],C.mem_verts_toSubgraph.mp hxC⟩
    rwa [hUj] at hh

lemma marked_group_between_visits_forces_ten
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (F : Finset (Fin k)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hFC : ∀ x ∈ (selectedGraph T F).support, x ∉ C.support)
    {a z b : V} (A : G.Walk a z) (B : G.Walk z b) (hAB : (A.append B).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append B).toSubgraph)
    (hprefix : ∀ x ∈ A.support, x ∈ (selectedGraph T F).support → x=z)
    (hmark : MarkedPartition (selectedGraph T F) F.card z)
    (hA : (C.toSubgraph.verts ∩ A.toSubgraph.verts).Nonempty)
    (hB : (C.toSubgraph.verts ∩ B.toSubgraph.verts).Nonempty) : 10 ≤ C.length := by
  obtain ⟨hleft,hright⟩ := marked_group_cut_intersections hfail T hs i j hij C hC hi F hiF hjF
    hFC A B hAB hj hprefix hmark
  have hleft := hleft hA
  have hright := hright hB
  have hzF : z ∈ (selectedGraph T F).support := by
    obtain ⟨D,d,P,_,_,hP,hnP,_⟩ := hmark
    exact path_support_subset_graph_support hP hnP z P.start_mem_support
  have hzC := hFC z hzF
  have hd : Disjoint (C.toSubgraph.verts ∩ A.toSubgraph.verts)
      (C.toSubgraph.verts ∩ B.toSubgraph.verts) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨hxC,hxA⟩ ⟨_,hxB⟩
    have hxz : x ≠ z := fun he ↦ hzC (he ▸ C.mem_verts_toSubgraph.mp hxC)
    exact hAB.ne_of_mem_support_of_append hxz (A.mem_verts_toSubgraph.mp hxA)
      (B.mem_verts_toSubgraph.mp hxB) rfl
  have hsub : (C.toSubgraph.verts ∩ A.toSubgraph.verts) ∪ (C.toSubgraph.verts ∩ B.toSubgraph.verts) ⊆
      C.toSubgraph.verts := by intro x hx; exact hx.elim And.left And.left
  have hc := Set.ncard_mono hsub
  have hCC : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [Set.ncard_union_eq hd,hCC] at hc
  omega

end Erdos583CarrierCutsDevelopment
