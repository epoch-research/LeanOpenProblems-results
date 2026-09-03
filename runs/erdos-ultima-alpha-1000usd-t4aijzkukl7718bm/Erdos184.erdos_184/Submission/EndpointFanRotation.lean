import Submission.EndpointFans

/-! Simultaneous endpoint rotations.  This file tracks actual simple paths,
not just the endpoint sequences of the preceding fan construction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Branch.fanStep_eq {L : List (Piece G)} (hL : Admissible L)
    {v a w : V} (ha : a ∈ (touchingEndpoints L v).erase v) (hb : Branch L v a w) :
    fanStep L v a = w := by
  have hw : w ∈ (coveredGraph L).neighborFinset v :=
    ((coveredGraph L).mem_neighborFinset v w).mpr hb.covered
  obtain ⟨b,hb'⟩ := (hL.branchMap_bijective v).2 ⟨w,hw⟩
  have hbw : (branchMap L v b).val = w := congrArg Subtype.val hb'
  have he : a = b.val := hb.endpoint_unique hL.1 (hbw ▸ branchMap_spec L v b)
  have hab : (⟨a,ha⟩ : {a // a ∈ (touchingEndpoints L v).erase v}) = b := Subtype.ext he
  rw [fanStep,dif_pos ha,hab]
  exact hbw

noncomputable def movedEndpoint (L : List (Piece G)) (v : V) (S : Finset V) (a : V) : V :=
  if a ∈ S then fanStep L v a else a

noncomputable def markedEdge (S : Finset V) (a : V) (e : Sym2 V) : List (Sym2 V) :=
  if a ∈ S then [e] else []

namespace FanRotation
variable {L : List (Piece G)} {v : V} (hL : Admissible L) (S : Finset V)
    (hS : S ⊆ (touchingEndpoints L v).erase v)
    (hSN : ∀ a ∈ S, G.Adj v a)
include hL hS hSN

/-- Reverse a selected arm about its center; unselected arms are unchanged. -/
lemma move_arm {a : V} (P : G.Walk v a) (hP : P.IsPath)
    (hbranch : ∀ (w : V) (hw : G.Adj v w) (Q : G.Walk w a),
      P = Walk.cons hw Q → Branch L v a w) :
    ∃ (b : V) (Q : G.Walk v b), b = movedEndpoint L v S a ∧
      Q.IsPath ∧ Q.support.Perm P.support ∧ Q.length = P.length ∧
      (Q.edges ++ markedEdge S a s(v,b)).Perm
        (P.edges ++ markedEdge S a s(v,a)) := by
  by_cases ha : a ∈ S
  · have hav : a ≠ v := (Finset.mem_erase.mp (hS ha)).1
    cases P with
    | nil => exact (hav rfl).elim
    | @cons v w a hw P =>
      have hva := hSN a ha
      have hPw := Walk.cons_isPath_iff hw P |>.mp hP
      let Q := Walk.cons hva P.reverse
      have he : w = movedEndpoint L v S a := by
        rw [movedEndpoint,if_pos ha]
        exact (Branch.fanStep_eq hL (hS ha) (hbranch w hw P rfl)).symm
      refine ⟨w,Q,he,?_,?_,?_,?_⟩
      · apply Walk.IsPath.cons hPw.1.reverse
        simpa only [Walk.support_reverse,List.mem_reverse] using hPw.2
      · simp only [Q,Walk.support_cons,Walk.support_reverse]
        exact (List.reverse_perm P.support).cons v
      · simp only [Q,Walk.length_cons,Walk.length_reverse]
      · apply List.perm_iff_count.mpr
        intro e
        simp only [Q,markedEdge,if_pos ha,Walk.edges_cons,Walk.edges_reverse,
          List.count_append,List.count_cons,List.count_nil,List.count_reverse]
        omega
  · refine ⟨a,P,by simp [movedEndpoint,ha],hP,List.Perm.refl _,rfl,?_⟩
    simp only [markedEdge,if_neg ha]
    exact List.Perm.refl _

omit [Fintype V] hL hS hSN in
lemma arms_inter {a b : V} (A : G.Walk v a) (B : G.Walk v b)
    (hp : (A.reverse.append B).IsPath) (x : V) (hx : x ∈ A.support) (hy : x ∈ B.support) :
    x = v := by
  by_contra hne
  have hx' : x ∈ A.reverse.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hx
  exact hp.ne_of_mem_support_of_append hne hx' hy rfl

/-- Apply independently the two endpoint rotations of a path through `v`.
The two arms remain internally disjoint because each keeps its vertex set. -/
lemma move_piece_through (p : Piece G) (hp : p ∈ L) (hv : v ∈ p.walk.support) :
    ∃ q : Piece G, q.src = movedEndpoint L v S p.src ∧
      q.dst = movedEndpoint L v S p.dst ∧ q.walk.support.Perm p.walk.support ∧
      q.walk.length = p.walk.length ∧
      (q.walk.edges ++ markedEdge S p.src s(v,q.src) ++ markedEdge S p.dst s(v,q.dst)).Perm
        (p.walk.edges ++ markedEdge S p.src s(v,p.src) ++ markedEdge S p.dst s(v,p.dst)) := by
  let A := (p.walk.takeUntil v hv).reverse
  let B := p.walk.dropUntil v hv
  have hAB : A.reverse.append B = p.walk := by simp only [A,B,Walk.reverse_reverse,Walk.take_spec]
  have hAp : A.IsPath := (p.isPath.takeUntil hv).reverse
  have hBp : B.IsPath := p.isPath.dropUntil hv
  have hAb (w : V) (hw : G.Adj v w) (Q : G.Walk w p.src)
      (he : A = Walk.cons hw Q) : Branch L v p.src w := by
    refine ⟨p,hp,hw,Or.inl ⟨rfl,?_⟩⟩
    rw [← hAB,Walk.darts_append]
    apply List.mem_append_left
    apply Walk.mem_darts_reverse.mpr
    rw [he]
    simp
  have hBb (w : V) (hw : G.Adj v w) (Q : G.Walk w p.dst)
      (he : B = Walk.cons hw Q) : Branch L v p.dst w := by
    refine ⟨p,hp,hw,Or.inr ⟨rfl,?_⟩⟩
    rw [← hAB,Walk.darts_append]
    apply List.mem_append_right
    rw [he]
    simp
  obtain ⟨a,A',ha,hA',hAs,hAl,hAe⟩ := move_arm hL S hS hSN A hAp hAb
  obtain ⟨b,B',hb,hB',hBs,hBl,hBe⟩ := move_arm hL S hS hSN B hBp hBb
  let P := A'.reverse.append B'
  have hP : P.IsPath := by
    apply append_isPath_of_support_inter hA'.reverse hB'
    intro x hx hy
    have hxA : x ∈ A.support := hAs.mem_iff.mp (by simpa using hx)
    have hyB : x ∈ B.support := hBs.mem_iff.mp hy
    exact arms_inter A B (hAB.symm ▸ p.isPath) x hxA hyB
  have hPl : P.length = p.walk.length := by
    rw [← hAB]
    simp only [P,Walk.length_append,Walk.length_reverse,hAl,hBl]
  have hab : a ≠ b := by
    intro he
    cases he
    have hnil := (Walk.isPath_iff_eq_nil P).mp hP
    have hz : p.walk.length = 0 := by rw [← hPl,hnil]; rfl
    exact p.ne (Walk.eq_of_length_eq_zero hz)
  let q : Piece G := ⟨a,b,P,hP,hab⟩
  refine ⟨q,ha,hb,?_,hPl,?_⟩
  · apply List.perm_ext_iff_of_nodup hP.support_nodup p.isPath.support_nodup |>.mpr
    intro x
    rw [← hAB]
    simp only [q,P,Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse]
    exact or_congr hAs.mem_iff hBs.mem_iff
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq hAe e
    have h₂ := List.Perm.count_eq hBe e
    rw [← hAB]
    simp only [q,P,Walk.edges_append,Walk.edges_reverse,List.count_append,List.count_reverse] at h₁ h₂ ⊢
    omega

end FanRotation
end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.FanRotation.move_piece_through
