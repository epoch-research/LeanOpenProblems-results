import Submission.ShortTriangleNonrootBound

/-! Necessary directed-predecessor constraints when a cycle and a touching path do not form two paths. -/
namespace Erdos583CyclePredecessorConstraintDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583Work.CycleFirstVisits Erdos583CycleFirstVisitRotationDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma nonabsorbable_first_predecessor {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b r u v : V} (C : G.Walk r r) (hC : C.IsCycle)
    (A : G.Walk a u) (D : G.Walk u b) (hp : (A.append D).IsPath)
    (hA : ∀ z ∈ A.support, z ∈ C.support → z=u)
    (hd : Disjoint C.toSubgraph.edgeSet (A.append D).toSubgraph.edgeSet)
    (hno : ¬TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ (A.append D).toSubgraph.edgeSet))
    (huv : C.toSubgraph.Adj u v) :
    ∃ w, ∃ E : G.Walk a w, ∃ f : G.Adj w v, ∃ B : G.Walk v b,
      A.append D=E.append (Walk.cons f B) ∧ w ∈ C.support := by
  classical
  have hvD : v ∈ D.support := by
    by_contra hvD
    apply hno
    simpa only [Set.union_comm] using cycle_missing_first_neighbor C hC A D hp hA huv hvD hd.symm
  obtain ⟨Q,hCQ,hQC⟩ := cycle_edge_first C hC (C.toSubgraph.adj_sub huv) (C.mem_edges_toSubgraph.mp huv)
  obtain ⟨w,R,f,hR⟩ := TerminalTail.nonnil_last_edge (D.takeUntil v hvD)
    (Walk.not_nil_of_ne huv.ne)
  let B := D.dropUntil v hvD
  have hD : D=R.append (Walk.cons f B) := by
    calc
      D=(D.takeUntil v hvD).append B := (Walk.take_spec D hvD).symm
      _=(R.concat f).append B := by rw [hR]
      _=R.append (Walk.cons f B) := by rw [Walk.concat_eq_append,←Walk.append_assoc,Walk.cons_nil_append]
  have hAQ (z : V) (hzA : z ∈ A.support) (hzC : z ∈ (Walk.cons (C.toSubgraph.adj_sub huv) Q).support) : z=u := by
    apply hA z hzA
    rwa [←Walk.mem_verts_toSubgraph,hQC,Walk.mem_verts_toSubgraph] at hzC
  obtain ⟨hQA,_,hX,hYX,hcover,_,hwA⟩ := cycle_first_visit_rotation (C.toSubgraph.adj_sub huv) Q hCQ
    A R f B (hD ▸ hp) hAQ (by rw [hQC,←hD]; exact hd)
  have hwC : w ∈ C.support := by
    by_contra hwC
    have hwQA : w ∉ (Q.append A.reverse).support := by
      rw [Walk.mem_support_append_iff]
      rintro (hh|hh)
      · apply hwC
        rw [←Walk.mem_verts_toSubgraph,←hQC,Walk.mem_verts_toSubgraph]
        exact List.mem_cons_of_mem _ hh
      · exact hwA (by simpa only [Walk.support_reverse,List.mem_reverse] using hh)
    have hY : (Walk.cons f (Q.append A.reverse)).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hQA,hwQA⟩
    apply hno
    refine ⟨w,a,w,b,Walk.cons f (Q.append A.reverse),R.reverse.append (Walk.cons (C.toSubgraph.adj_sub huv) B),
      hY,hX,hYX,?_⟩
    simpa only [hQC,←hD] using hcover
  exact ⟨w,A.append R,f,B,by rw [hD,Walk.append_assoc],hwC⟩

lemma path_no_opposite_steps {V : Type*} {G : SimpleGraph V} {a b x y : V}
    (P : G.Walk a b) (hp : P.IsPath) (A : G.Walk a x) (f : G.Adj x y) (B : G.Walk y b)
    (D : G.Walk a y) (g : G.Adj y x) (E : G.Walk x b)
    (hP : P=A.append (Walk.cons f B)) (hP' : P=D.append (Walk.cons g E)) : False := by
  have ha : A.length ≤ P.length := by rw [hP,Walk.length_append,Walk.length_cons]; omega
  have ha' : A.length+1 ≤ P.length := by rw [hP,Walk.length_append,Walk.length_cons]; omega
  have hd : D.length ≤ P.length := by rw [hP',Walk.length_append,Walk.length_cons]; omega
  have hd' : D.length+1 ≤ P.length := by rw [hP',Walk.length_append,Walk.length_cons]; omega
  have hax : P.getVert A.length=x := by rw [hP,Walk.getVert_append]; simp
  have hay : P.getVert (A.length+1)=y := by rw [hP,Walk.getVert_append]; simp
  have hdy : P.getVert D.length=y := by rw [hP',Walk.getVert_append]; simp
  have hdx : P.getVert (D.length+1)=x := by rw [hP',Walk.getVert_append]; simp
  have h1 := hp.getVert_injOn ha hd' (hax.trans hdx.symm)
  have h2 := hp.getVert_injOn ha' hd (hay.trans hdy.symm)
  omega

end Erdos583CyclePredecessorConstraintDevelopment
