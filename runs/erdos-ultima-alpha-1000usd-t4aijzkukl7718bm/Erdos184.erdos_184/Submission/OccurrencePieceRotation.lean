import Submission.OccurrenceFanBranches

/-! Rotating chosen endpoint occurrences while allowing repeated endpoint labels. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OccurrenceFan
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def moveEnd (f : V → V) (S : Finset V) (a : V) : V :=
  if a ∈ S then f a else a

section Arms
variable (f : V → V) (S : Finset V) {v : V}
    (hSv : ∀ a ∈ S, a ≠ v) (hSN : ∀ a ∈ S, G.Adj v a)
include hSv hSN

/-- Reverse a selected arm about its center; unselected arms are unchanged. -/
lemma move_arm {a : V} (P : G.Walk v a) (hP : P.IsPath)
    (hstep : a ∈ S → f a = P.snd) :
    ∃ (b : V) (Q : G.Walk v b), b = moveEnd f S a ∧
      Q.IsPath ∧ Q.support.Perm P.support ∧ Q.length = P.length ∧
      (Q.edges ++ markedEdge S a s(v,b)).Perm
        (P.edges ++ markedEdge S a s(v,a)) := by
  by_cases ha : a ∈ S
  · have hav : a ≠ v := hSv a ha
    cases P with
    | nil => exact (hav rfl).elim
    | @cons v w a hw P =>
      have hva := hSN a ha
      have hPw := Walk.cons_isPath_iff hw P |>.mp hP
      let Q := Walk.cons hva P.reverse
      have he : w = moveEnd f S a := by
        rw [moveEnd,if_pos ha]
        simpa using (hstep ha).symm
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
  · refine ⟨a,P,by simp [moveEnd,ha],hP,List.Perm.refl _,rfl,?_⟩
    simp only [markedEdge,if_neg ha]
    exact List.Perm.refl _

/-- Apply independently the two endpoint rotations of a path through `v`.
The two arms remain internally disjoint because each keeps its vertex set. -/
lemma move_piece_through (p : Piece G) (hv : v ∈ p.walk.support)
    (hs : p.src ∈ S → f p.src = (p.walk.takeUntil v hv).reverse.snd)
    (ht : p.dst ∈ S → f p.dst = (p.walk.dropUntil v hv).snd) :
    ∃ q : Piece G, q.src = moveEnd f S p.src ∧
      q.dst = moveEnd f S p.dst ∧ q.walk.support.Perm p.walk.support ∧
      q.walk.length = p.walk.length ∧
      (q.walk.edges ++ markedEdge S p.src s(v,q.src) ++ markedEdge S p.dst s(v,q.dst)).Perm
        (p.walk.edges ++ markedEdge S p.src s(v,p.src) ++ markedEdge S p.dst s(v,p.dst)) := by
  let A := (p.walk.takeUntil v hv).reverse
  let B := p.walk.dropUntil v hv
  have hAB : A.reverse.append B = p.walk := by simp only [A,B,Walk.reverse_reverse,Walk.take_spec]
  have hAp : A.IsPath := (p.isPath.takeUntil hv).reverse
  have hBp : B.IsPath := p.isPath.dropUntil hv
  obtain ⟨a,A',ha,hA',hAs,hAl,hAe⟩ := move_arm f S hSv hSN A hAp hs
  obtain ⟨b,B',hb,hB',hBs,hBl,hBe⟩ := move_arm f S hSv hSN B hBp ht
  let P := A'.reverse.append B'
  have hP : P.IsPath := by
    apply append_isPath_of_support_inter hA'.reverse hB'
    intro x hx hy
    have hxA : x ∈ A.support := hAs.mem_iff.mp (by simpa using hx)
    have hyB : x ∈ B.support := hBs.mem_iff.mp hy
    exact FanRotation.arms_inter A B (hAB.symm ▸ p.isPath) x hxA hyB
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

end Arms
end Erdos184Work.OddPaths.OccurrenceFan
