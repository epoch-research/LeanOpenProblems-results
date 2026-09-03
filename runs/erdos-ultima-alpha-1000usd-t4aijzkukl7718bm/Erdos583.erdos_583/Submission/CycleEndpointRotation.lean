import Submission.Work

/-! A Pósa rotation between a whole cycle and a path whose endpoint is on
that cycle. The transferred edge leaves a path or a shorter lollipop. -/
namespace Erdos583CycleEndpointRotationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma cycle_endpoint_rotation {V : Type*} {G : SimpleGraph V} {u v w b : V}
    (h : G.Adj u v) (Q : G.Walk v u) (hC : (Walk.cons h Q).IsCycle)
    (A : G.Walk u w) (f : G.Adj w v) (B : G.Walk v b)
    (hp : (A.append (Walk.cons f B)).IsPath)
    (hd : Disjoint (Walk.cons h Q).toSubgraph.edgeSet
      (A.append (Walk.cons f B)).toSubgraph.edgeSet) :
    (Walk.cons f Q).IsTrail ∧
      (A.reverse.append (Walk.cons h B)).IsPath ∧
      Disjoint (Walk.cons f Q).toSubgraph.edgeSet
        (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet ∧
      (Walk.cons f Q).toSubgraph.edgeSet ∪
          (A.reverse.append (Walk.cons h B)).toSubgraph.edgeSet=
        (Walk.cons h Q).toSubgraph.edgeSet ∪
          (A.append (Walk.cons f B)).toSubgraph.edgeSet ∧
      (A.reverse.append (Walk.cons h B)).toSubgraph.verts=
        (A.append (Walk.cons f B)).toSubgraph.verts ∧
      (Walk.cons f Q).toSubgraph.verts=insert w (Walk.cons h Q).toSubgraph.verts ∧ w ≠ u := by
  classical
  have hQ := (Walk.cons_isCycle_iff Q h).mp hC |>.1
  have hAB := TriangleAbsorption.append_cons_support_disjoint A f B hp
  have huB : u ∉ B.support := fun hu ↦ hAB u A.start_mem_support hu
  have hQB : (Walk.cons h B).IsPath := (Walk.cons_isPath_iff h B).mpr
    ⟨hp.of_append_right.of_cons,huB⟩
  have hX : (A.reverse.append (Walk.cons h B)).IsPath := by
    apply path_append_of_support_intersection hp.of_append_left.reverse hQB
    intro x hxA hxB
    have hxA' : x ∈ A.support := by simpa using hxA
    rcases List.mem_cons.mp hxB with hx | hx
    · exact hx
    · exact (hAB x hxA' hx).elim
  have hfP : s(w,v) ∈ (A.append (Walk.cons f B)).toSubgraph.edgeSet := by
    simp
  have hfC : s(w,v) ∉ (Walk.cons h Q).edges := fun he ↦
    Set.disjoint_left.mp hd ((Walk.cons h Q).mem_edges_toSubgraph.mpr he) hfP
  have hfQ : s(w,v) ∉ Q.edges := fun he ↦ hfC (List.mem_cons_of_mem _ he)
  have hY : (Walk.cons f Q).IsTrail := (Walk.isTrail_cons f Q).mpr ⟨hQ.isTrail,hfQ⟩
  have hw : w ≠ u := by
    intro hwu
    exact hfC (by subst w; simp)
  have hfA : s(w,v) ∉ A.edges := by
    intro he
    have hh := RootedTailSystem.append_trail_disjoint hp.isTrail
    exact Set.disjoint_left.mp hh (A.mem_edges_toSubgraph.mpr he)
      ((Walk.cons f B).mem_edges_toSubgraph.mpr (by simp))
  have hfB : s(w,v) ∉ B.edges := (Walk.isTrail_cons f B).mp hp.of_append_right.isTrail |>.2
  have hhQ : s(u,v) ∉ Q.edges := (Walk.isTrail_cons h Q).mp hC.isTrail |>.2
  have hQold (e : Sym2 V) (heQ : e ∈ Q.edges) (heP : e ∈ (A.append (Walk.cons f B)).edges) : False :=
    Set.disjoint_left.mp hd
      ((Walk.cons h Q).mem_edges_toSubgraph.mpr (List.mem_cons_of_mem _ heQ))
      ((A.append (Walk.cons f B)).mem_edges_toSubgraph.mpr heP)
  refine ⟨hY,hX,?_,?_,?_,?_,hw⟩
  · apply Set.disjoint_left.mpr
    intro e heY heX
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_append,List.mem_cons,
      List.mem_append,Walk.edges_reverse,List.mem_reverse] at heY heX
    rcases heY with rfl | heQ
    · rcases heX with heA | heH | heB
      · exact hfA heA
      · exact hfC (List.mem_cons.mpr (Or.inl heH))
      · exact hfB heB
    · rcases heX with heA | rfl | heB
      · exact hQold e heQ (by simp [heA])
      · exact hhQ heQ
      · exact hQold e heQ (by simp [heB])
  · ext e
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_append,
      List.mem_cons,List.mem_append,Walk.edges_reverse,List.mem_reverse]
    tauto
  · ext x
    simp only [Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff,Walk.support_reverse,
      List.mem_reverse,Walk.support_cons,List.mem_cons]
    constructor
    · rintro (hx | rfl | hx)
      · exact Or.inl hx
      · exact Or.inl A.start_mem_support
      · exact Or.inr (Or.inr hx)
    · rintro (hx | rfl | hx)
      · exact Or.inl hx
      · exact Or.inl A.end_mem_support
      · exact Or.inr (Or.inr hx)
  · ext x
    simp only [Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons,Set.mem_insert_iff]
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
    · rintro (hx | rfl | hx)
      · exact Or.inl hx
      · exact Or.inr Q.end_mem_support
      · exact Or.inr hx

end Erdos583CycleEndpointRotationDevelopment
