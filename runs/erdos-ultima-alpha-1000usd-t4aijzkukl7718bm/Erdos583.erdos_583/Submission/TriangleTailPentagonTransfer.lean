import Submission.TriangleTailRootLocked

/-! A short rooted triangle with another endpoint at its root yields a whole pentagon. -/
namespace Erdos583TriangleTailPentagonTransferDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583TriangleTailRootTemplatesDevelopment Erdos583TriangleTailRootLockedDevelopment
open Erdos583LollipopEndpointRotationDevelopment Erdos583RootEndpointTailCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma two_visits_in_one_order {V : Type*} {G : SimpleGraph V} {a b x y : V}
    (P : G.Walk a b) (hx : x ∈ P.support) (hy : y ∈ P.support) :
    (∃ A : G.Walk a x, ∃ B : G.Walk x y, ∃ D : G.Walk y b, P=A.append (B.append D)) ∨
    (∃ A : G.Walk a y, ∃ B : G.Walk y x, ∃ D : G.Walk x b, P=A.append (B.append D)) := by
  obtain ⟨A,E,hP⟩ := P.mem_support_iff_exists_append.mp hx
  by_cases hyE : y ∈ E.support
  · obtain ⟨B,D,hE⟩ := E.mem_support_iff_exists_append.mp hyE
    exact Or.inl ⟨A,B,D,by rw [hP,hE]⟩
  · have hyA : y ∈ A.support := ((Walk.mem_support_append_iff A E).mp (hP ▸ hy)).resolve_right hyE
    obtain ⟨B,D,hA⟩ := A.mem_support_iff_exists_append.mp hyA
    exact Or.inr ⟨B,D,E,by rw [hP,hA,Walk.append_assoc]⟩

lemma replace_defect_by_whole_cycle {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (hi : ¬(T.walk i).IsPath)
    {r a b : V} (C : G.Walk r r) (P : G.Walk a b) (hC : C.IsCycle) (hP : P.IsPath)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (he : C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet=
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (U.walk i).toSubgraph=C.toSubgraph := by
  obtain ⟨U,hUi,_,_,hscore⟩ := GeneralPair.replace_two T i j hij r r a b C P hC.isTrail hP.isTrail hd he
  obtain ⟨hdef,hother⟩ := T.one_defect_other_paths hs i hi
  have hv : (T.walk i).toSubgraph.verts.ncard=(T.walk i).length := by
    have hh := T.defect_add_vertices i
    rw [hdef] at hh
    omega
  have hl := congrArg Set.ncard he
  rw [Set.ncard_union_eq hd,Set.ncard_union_eq (T.disjoint hij),trail_edgeSet_ncard C hC.isTrail,
    trail_edgeSet_ncard P hP.isTrail,trail_edgeSet_ncard _ (T.isTrail i),trail_edgeSet_ncard _ (T.isTrail j)] at hl
  have hCv : C.toSubgraph.verts.ncard=C.length := by rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [hv,hCv,InducedBuffer.path_vertex_ncard _ (hother j hij.symm),InducedBuffer.path_vertex_ncard _ hP] at hscore
  exact ⟨U,by omega,hUi⟩

lemma ordered_triangle_tail_pentagon_transfer {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r)
    (hmin : ∀ W : TrailFamily G k, ∀ u : V, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    {x y s t b : V} (F : Frame G r x y s t)
    (hxC : L.cycle.toSubgraph.Adj r x) (hyC : L.cycle.toSubgraph.Adj r y)
    (hS : L.tail.support=[r,s,t]) (hi : (T.walk L.index).toSubgraph.edgeSet=F.edges)
    (j : Fin k) (hij : L.index ≠ j)
    (A : G.Walk r x) (B : G.Walk x y) (D : G.Walk y b)
    (hp : (A.append (B.append D)).IsPath)
    (hj : (T.walk j).toSubgraph=(A.append (B.append D)).toSubgraph) :
    ∃ U : TrailFamily G k, ∃ C : G.Walk r r,
      U.score=T.score ∧ C.IsCycle ∧ C.length=5 ∧ (U.walk L.index).toSubgraph=C.toSubgraph := by
  classical
  obtain ⟨w,R,f,hA⟩ := TerminalTail.nonnil_last_edge A (Walk.not_nil_of_ne F.rx.ne)
  obtain ⟨z,Q,g,hB⟩ := TerminalTail.nonnil_last_edge B (Walk.not_nil_of_ne F.xy.ne)
  have hform : A.append (B.append D)=R.append (Walk.cons f (Q.append (Walk.cons g D))) := by
    rw [hA,hB,Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
    rw [Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  have hform' : A.append (B.append D)=(R.append (Walk.cons f Q)).append (Walk.cons g D) := by
    rw [hform,←Walk.cons_append,Walk.append_assoc]
  have hp' := hform ▸ hp
  have hj' := hj.trans (congrArg Walk.toSubgraph hform)
  have hpred (u v : V) (hu : L.cycle.toSubgraph.Adj r u)
      (E : G.Walk r v) (h : G.Adj v u) (J : G.Walk u b)
      (hP : A.append (B.append D)=E.append (Walk.cons h J)) : v=s ∨ v=t := by
    obtain ⟨a,W,f',Z,hpform,haS,haC⟩ := minimum_lollipop_root_path_predecessor T hm r L hmin j hij hu
      (A.append (B.append D)) hp hj
    have hav : a=v := by
      have hWx : (A.append (B.append D)).getVert (W.length+1)=u := by
        rw [hpform,Walk.getVert_append]; simp
      have hEu : (A.append (B.append D)).getVert (E.length+1)=u := by
        rw [hP,Walk.getVert_append]; simp
      have hidx : W.length+1=E.length+1 := by
        apply hp.getVert_injOn
        · change W.length+1 ≤ (A.append (B.append D)).length
          rw [hpform,Walk.length_append,Walk.length_cons]; omega
        · change E.length+1 ≤ (A.append (B.append D)).length
          rw [hP,Walk.length_append,Walk.length_cons]; omega
        · exact hWx.trans hEu.symm
      have hlen : W.length=E.length := by omega
      have h1 : (A.append (B.append D)).getVert W.length=a := by rw [hpform,Walk.getVert_append]; simp
      have h2 : (A.append (B.append D)).getVert E.length=v := by rw [hP,Walk.getVert_append]; simp
      rw [hlen] at h1
      exact h1.symm.trans h2
    have hvS : v ∈ L.tail.support := hav ▸ haS
    have hvr : v ≠ r := fun he ↦ haC (hav.symm ▸ he ▸ L.cycle.start_mem_support)
    rw [hS] at hvS
    simpa only [List.mem_cons,List.not_mem_nil,or_false,or_iff_right hvr] using hvS
  have hw := hpred x w hxC R f (Q.append (Walk.cons g D)) hform
  have hz := hpred y z hyC (R.append (Walk.cons f Q)) g D hform'
  have hwz : w ≠ z := by
    intro he
    subst z
    exact F.xy.ne (path_same_predecessor_same_successor (A.append (B.append D)) hp
      R f (Q.append (Walk.cons g D)) (R.append (Walk.cons f Q)) g D hform hform')
  have hd : Disjoint (R.append (Walk.cons f (Q.append (Walk.cons g D)))).toSubgraph.edgeSet F.edges := by
    rw [←hj',←hi]; exact T.disjoint hij.symm
  have hno : ¬TwoPathCover (G := G)
      ((R.append (Walk.cons f (Q.append (Walk.cons g D)))).toSubgraph.edgeSet ∪ F.edges) := by
    intro hc
    apply ShortLollipop.maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
    rw [hi,hj',Set.union_comm]
    exact hc
  rcases hw with rfl | rfl
  · rcases hz with hz | rfl
    · exact (hwz hz.symm).elim
    · exact (hno (inner_first_always_absorbs F R f Q g D hp' hd)).elim
  · rcases hz with rfl | hz
    · obtain ⟨⟨e,hR⟩,⟨h,hQ⟩⟩ := outer_first_locked F R f Q g D hp' hd hno
      have hPform : R.append (Walk.cons f (Q.append (Walk.cons g D)))=
          Walk.cons e (Walk.cons f (Walk.cons h (Walk.cons g D))) := by
        rw [hR,hQ]; rfl
      obtain ⟨C,P,hC,hCl,hP,hCP,hcover⟩ := locked_whole_pentagon F e f h g D
        (hPform ▸ hp') (hPform ▸ hd)
      obtain ⟨U,hUs,hUi⟩ := replace_defect_by_whole_cycle T hs L.index j hij L.member_not_path
        C P hC hP hCP (by rw [hcover,←hPform,←hi,←hj'])
      exact ⟨U,C,hUs,hC,hCl,hUi⟩
    · exact (hwz hz.symm).elim

end Erdos583TriangleTailPentagonTransferDevelopment
