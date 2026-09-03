import Submission.TriangleTailRootTemplates

/-! The nonabsorbable ordered root-start pattern is a five-vertex core. -/
namespace Erdos583TriangleTailRootLockedDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TriangleAbsorption Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583TriangleTailRootTemplatesDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma inner_first_always_absorbs {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t b : V}
    (F : Frame G r x y s t) (A : G.Walk r s) (f : G.Adj s x)
    (B : G.Walk x t) (h : G.Adj t y) (D : G.Walk y b)
    (hp : (A.append (Walk.cons f (B.append (Walk.cons h D)))).IsPath)
    (hd : Disjoint (A.append (Walk.cons f (B.append (Walk.cons h D)))).toSubgraph.edgeSet F.edges) :
    TwoPathCover (G := G) ((A.append (Walk.cons f (B.append (Walk.cons h D)))).toSubgraph.edgeSet ∪ F.edges) := by
  obtain ⟨a,R,g,hA⟩ := TerminalTail.nonnil_last_edge A (Walk.not_nil_of_ne F.rs.ne)
  have hform : A.append (Walk.cons f (B.append (Walk.cons h D)))=
      R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D)))) := by
    rw [hA,Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  have har : a ≠ r := by
    intro he
    have hedge : s(a,s) ∈ (A.append (Walk.cons f (B.append (Walk.cons h D)))).toSubgraph.edgeSet := by
      rw [hform]; simp
    exact Set.disjoint_left.mp hd hedge (by simp [Frame.edges,he])
  rw [hform] at hp hd ⊢
  exact inner_first_absorption F R g f B h D hp har hd

lemma outer_first_locked {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t b : V}
    (F : Frame G r x y s t) (A : G.Walk r t) (f : G.Adj t x)
    (B : G.Walk x s) (h : G.Adj s y) (D : G.Walk y b)
    (hp : (A.append (Walk.cons f (B.append (Walk.cons h D)))).IsPath)
    (hd : Disjoint (A.append (Walk.cons f (B.append (Walk.cons h D)))).toSubgraph.edgeSet F.edges)
    (hno : ¬TwoPathCover (G := G) ((A.append (Walk.cons f (B.append (Walk.cons h D)))).toSubgraph.edgeSet ∪ F.edges)) :
    (∃ e : G.Adj r t, A=Walk.cons e Walk.nil) ∧ (∃ g : G.Adj x s, B=Walk.cons g Walk.nil) := by
  obtain ⟨a,R,g,hA⟩ := TerminalTail.nonnil_last_edge A (Walk.not_nil_of_ne F.tr.symm)
  have hform : A.append (Walk.cons f (B.append (Walk.cons h D)))=
      R.append (Walk.cons g (Walk.cons f (B.append (Walk.cons h D)))) := by
    rw [hA,Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  have har : a=r := by
    by_contra har
    apply hno
    rw [hform]
    exact outer_first_long_prefix_absorption F R g f B h D (hform ▸ hp) har (hform ▸ hd)
  subst a
  have hR : R=Walk.nil := (Walk.isPath_iff_eq_nil R).mp ((hform ▸ hp).of_append_left)
  have hAe : A=Walk.cons g Walk.nil := by rw [hA,hR]; rfl
  refine ⟨⟨g,hAe⟩,?_⟩
  rw [hAe,Walk.cons_nil_append] at hp hd hno
  obtain ⟨a,Q,j,hB⟩ := TerminalTail.nonnil_last_edge B (Walk.not_nil_of_ne F.sx.symm)
  have hformB : Walk.cons g (Walk.cons f (B.append (Walk.cons h D)))=
      Walk.cons g (Walk.cons f (Q.append (Walk.cons j (Walk.cons h D)))) := by
    rw [hB,Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  have hax : a=x := by
    by_contra hax
    apply hno
    rw [hformB]
    exact outer_first_long_middle_absorption F g f Q j h D (hformB ▸ hp) hax (hformB ▸ hd)
  subst a
  have hQ : Q=Walk.nil := (Walk.isPath_iff_eq_nil Q).mp ((hformB ▸ hp).of_cons.of_cons.of_append_left)
  exact ⟨j,by rw [hB,hQ]; rfl⟩

lemma locked_whole_pentagon {V : Type*} [Fintype V] {G : SimpleGraph V} {r x y s t b : V}
    (F : Frame G r x y s t) (e : G.Adj r t) (f : G.Adj t x)
    (g : G.Adj x s) (h : G.Adj s y) (D : G.Walk y b)
    (hp : (Walk.cons e (Walk.cons f (Walk.cons g (Walk.cons h D)))).IsPath)
    (hd : Disjoint (Walk.cons e (Walk.cons f (Walk.cons g (Walk.cons h D)))).toSubgraph.edgeSet F.edges) :
    ∃ C : G.Walk r r, ∃ P : G.Walk t b,
      C.IsCycle ∧ C.length=5 ∧ P.IsPath ∧ Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet ∧
      C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet =
        F.edges ∪ (Walk.cons e (Walk.cons f (Walk.cons g (Walk.cons h D)))).toSubgraph.edgeSet := by
  let C := Walk.cons F.rx (Walk.cons F.xy (Walk.cons h.symm (Walk.cons F.st (Walk.cons e.symm Walk.nil))))
  let P := Walk.cons f (Walk.cons g (Walk.cons F.rs.symm (Walk.cons F.ry D)))
  have hD := hp.of_cons.of_cons.of_cons.of_cons
  have hrD : r ∉ D.support := fun hh ↦ (Walk.cons_isPath_iff e _).mp hp |>.2 (by simp [hh])
  have htD : t ∉ D.support := fun hh ↦ (Walk.cons_isPath_iff f _).mp hp.of_cons |>.2 (by simp [hh])
  have hxD : x ∉ D.support := fun hh ↦ (Walk.cons_isPath_iff g _).mp hp.of_cons.of_cons |>.2 (by simp [hh])
  have hsD : s ∉ D.support := (Walk.cons_isPath_iff h _).mp hp.of_cons.of_cons.of_cons |>.2
  have hP : P.IsPath := by
    simp only [P,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨⟨hD,hrD⟩,F.rs.ne.symm,hsD⟩,g.ne,F.rx.ne.symm,hxD⟩,F.tx,F.st.ne.symm,F.tr,htD⟩
  have hC : C.IsCycle := by
    simp only [C,Walk.cons_isCycle_iff,Walk.isPath_def,Walk.support_cons,Walk.support_nil,
      List.nodup_cons,List.nodup_nil,and_true,List.mem_cons,List.not_mem_nil,or_false,not_or,
      Walk.edges_cons,Walk.edges_nil]
    simp only [not_or,Sym2.eq_iff,not_and_or]
    aesop
  have hlen : C.length=5 := rfl
  have he : C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet =
      F.edges ∪ (Walk.cons e (Walk.cons f (Walk.cons g (Walk.cons h D)))).toSubgraph.edgeSet := by
    ext q
    simp only [C,P,Frame.edges,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := y) (b := s),Sym2.eq_swap (a := t) (b := r),Sym2.eq_swap (a := s) (b := r)]
    tauto
  have hcard : C.length+P.length=
      (F.edges ∪ (Walk.cons e (Walk.cons f (Walk.cons g (Walk.cons h D)))).toSubgraph.edgeSet).ncard := by
    rw [Set.union_comm,F.union_ncard _ hp hd]
    simp only [C,P,Walk.length_cons,Walk.length_nil]
    omega
  exact ⟨C,P,hC,hlen,hP,disjoint_of_cover_length C P hC.isTrail hP.isTrail _ he hcard,he⟩

end Erdos583TriangleTailRootLockedDevelopment
