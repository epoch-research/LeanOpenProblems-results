import Submission.TwoEndpointFanRotation

/-! Absorption after simultaneous branch-fan rotation, when the two terminal
paths are vertex-disjoint.  Disjointness is an explicit hypothesis. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} {G : SimpleGraph V}

namespace Piece
lemma ending_at (p : Piece G) {t : V} (ht : t = p.src ∨ t = p.dst) :
    ∃ (a : V) (P : G.Walk a t), P.IsPath ∧ P.support.Perm p.walk.support ∧
      P.edges.Perm p.walk.edges ∧ [a,t].Perm [p.src,p.dst] := by
  rcases ht with rfl | rfl
  · refine ⟨p.dst,p.walk.reverse,p.isPath.reverse,?_,?_,?_⟩
    · simpa only [Walk.support_reverse] using List.reverse_perm p.walk.support
    · simpa only [Walk.edges_reverse] using List.reverse_perm p.walk.edges
    · exact List.Perm.swap ..
  · exact ⟨p.src,p.walk,p.isPath,List.Perm.refl _,List.Perm.refl _,List.Perm.refl _⟩

lemma starting_at (p : Piece G) {t : V} (ht : t = p.src ∨ t = p.dst) :
    ∃ (b : V) (P : G.Walk t b), P.IsPath ∧ P.support.Perm p.walk.support ∧
      P.edges.Perm p.walk.edges ∧ [t,b].Perm [p.src,p.dst] := by
  rcases ht with rfl | rfl
  · exact ⟨p.dst,p.walk,p.isPath,List.Perm.refl _,List.Perm.refl _,List.Perm.refl _⟩
  · refine ⟨p.src,p.walk.reverse,p.isPath.reverse,?_,?_,?_⟩
    · simpa only [Walk.support_reverse] using List.reverse_perm p.walk.support
    · simpa only [Walk.edges_reverse] using List.reverse_perm p.walk.edges
    · exact List.Perm.swap ..
end Piece

namespace FanAbsorption
lemma join_endpoint_paths (p q : Piece G) {v t z : V}
    (ht : t = p.src ∨ t = p.dst) (hz : z = q.src ∨ z = q.dst)
    (hvt : G.Adj v t) (hvz : G.Adj v z)
    (hvp : v ∉ p.walk.support) (hvq : v ∉ q.walk.support)
    (hdis : p.walk.support.Disjoint q.walk.support) :
    ∃ r : Piece G,
      r.walk.edges.Perm (p.walk.edges ++ q.walk.edges ++ [s(v,t),s(v,z)]) ∧
      [r.src,r.dst,t,z].Perm [p.src,p.dst,q.src,q.dst] := by
  obtain ⟨a,P,hP,hPs,hPe,hPv⟩ := p.ending_at ht
  obtain ⟨b,Q,hQ,hQs,hQe,hQv⟩ := q.starting_at hz
  have hvP : v ∉ P.support := fun h => hvp (hPs.mem_iff.mp h)
  have hvQ : v ∉ Q.support := fun h => hvq (hQs.mem_iff.mp h)
  have hPQ : P.support.Disjoint Q.support := by
    intro x hx hy
    exact hdis (hPs.mem_iff.mp hx) (hQs.mem_iff.mp hy)
  let R := (P.concat hvt.symm).append (Walk.cons hvz Q)
  have hR : R.IsPath := by
    apply Absorption.join_isPath P (Walk.cons hvz Q) hP (hQ.cons hvQ) hvt.symm
    intro x hx hy
    simp only [Walk.support_cons,List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hvP hx
    · exact hPQ hx hy
  have hab : a ≠ b := by
    intro he
    exact hPQ P.start_mem_support (he.symm ▸ Q.end_mem_support)
  let r : Piece G := ⟨a,b,R,hR,hab⟩
  refine ⟨r,?_,?_⟩
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq hPe e
    have h₂ := List.Perm.count_eq hQe e
    simp only [r,R,Walk.edges_append,Walk.edges_concat,Walk.edges_cons,List.concat_eq_append,
      List.count_append,List.count_cons,List.count_nil,show s(t,v) = s(v,t) from Sym2.eq_swap] at h₁ h₂ ⊢
    omega
  · apply List.perm_iff_count.mpr
    intro x
    have h₁ := List.Perm.count_eq hPv x
    have h₂ := List.Perm.count_eq hQv x
    simp only [r,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega

variable [Fintype V]

/-- No disjoint terminal paths can occur after a valid two-fan rotation
around an unused cycle.  The family `M` may have repeated endpoints. -/
lemma no_disjoint_terminal_paths {L M : List (Piece G)} (hL : Maximal L)
    {v x y t z : V} (Q : G.Walk x y) (hx : G.Adj v x) (hy : G.Adj y v)
    (hC : (Walk.cons hx (Q.concat hy)).IsCycle)
    (hunused : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges)
    (he : (edgeList M ++ [s(v,t),s(v,z)]).Perm (edgeList L ++ [s(v,x),s(v,y)]))
    (hv : (endpoints M ++ [x,y]).Perm (endpoints L ++ [t,z]))
    (hvt : G.Adj v t) (hvz : G.Adj v z)
    (p q : Piece G) (hp : p ∈ M) (hq : q ∈ M)
    (ht : t = p.src ∨ t = p.dst) (hz : z = q.src ∨ z = q.dst)
    (hvp : v ∉ p.walk.support) (hvq : v ∉ q.walk.support)
    (hdis : p.walk.support.Disjoint q.walk.support) : False := by
  have hqp : q ≠ p := by
    intro heq
    exact hdis p.walk.start_mem_support (heq.symm ▸ p.walk.start_mem_support)
  obtain ⟨N,hN⟩ := two_at_front hp hq hqp
  have hedgeN := edgeList_perm hN
  have hendN := endpoints_perm hN
  obtain ⟨r,hrE,hrV⟩ := join_endpoint_paths p q ht hz hvt hvz hvp hvq hdis
  have hQ : Q.IsPath := (Walk.concat_isPath_iff hy).mp
    ((Walk.cons_isCycle_iff (Q.concat hy) hx).mp hC).1 |>.1
  have hxy : x ≠ y := by
    intro hxy
    cases hxy
    have hnil := (Walk.isPath_iff_eq_nil Q).mp hQ
    have hl := hC.three_le_length
    simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
    omega
  let qR : Piece G := ⟨x,y,Q,hQ,hxy⟩
  have hfinalE : (edgeList (r :: qR :: N)).Perm
      (edgeList L ++ (Walk.cons hx (Q.concat hy)).edges) := by
    apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq hedgeN e
    have h₃ := List.Perm.count_eq hrE e
    simp only [qR,edgeList_cons,Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,
      List.count_append,List.count_cons,List.count_nil,
      show s(y,v) = s(v,y) from Sym2.eq_swap] at h₁ h₂ h₃ ⊢
    omega
  have hfinalV : (endpoints (r :: qR :: N)).Perm (endpoints L) := by
    apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq hendN a
    have h₃ := List.Perm.count_eq hrV a
    simp only [qR,endpoints_cons,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ h₃ ⊢
    omega
  exact hL.no_exchange hC.isTrail.edges_nodup (by simp) hunused hfinalE hfinalV

end FanAbsorption
end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.FanAbsorption.join_endpoint_paths
#print axioms Erdos184Work.OddPaths.FanAbsorption.no_disjoint_terminal_paths
