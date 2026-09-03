import Submission.OneEndpointFanRotation
import Submission.FanCycleAbsorption

/-! A single endpoint path meeting an unused cycle only at that endpoint
can absorb the cycle after a single fan rotation. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} {G : SimpleGraph V}
namespace FanAbsorption

lemma extend_clean_pair (p q : Piece G) {v x t : V}
    (Q : G.Walk x v) (hQ : Q.IsPath) (hvx : G.Adj v x) (hvt : G.Adj v t)
    (hpv : v = p.src ∨ v = p.dst) (hqt : t = q.src ∨ t = q.dst)
    (hvq : v ∉ q.walk.support)
    (hclean : ∀ a, a ∈ p.walk.support → a ∈ Q.support → a = v) :
    ∃ r s : Piece G,
      (r.walk.edges ++ s.walk.edges).Perm (p.walk.edges ++ q.walk.edges ++ Q.edges ++ [s(v,t)]) ∧
      [r.src,r.dst,s.src,s.dst,t].Perm [p.src,p.dst,q.src,q.dst,x] := by
  obtain ⟨a,P,hP,hPs,hPe,hPv⟩ := p.ending_at hpv
  obtain ⟨b,R,hR,hRs,hRe,hRv⟩ := q.starting_at hqt
  have hPQ : (P.append Q.reverse).IsPath := by
    apply append_isPath_of_support_inter hP hQ.reverse
    intro y hy hz
    exact hclean y (hPs.mem_iff.mp hy) (by simpa only [Walk.support_reverse,List.mem_reverse] using hz)
  have hax : a ≠ x := by
    intro he
    have hh := hclean a (hPs.mem_iff.mp P.start_mem_support) (he.symm ▸ Q.start_mem_support)
    exact hvx.ne (hh.symm.trans he)
  have hvR : v ∉ R.support := fun h => hvq (hRs.mem_iff.mp h)
  have hvb : v ≠ b := fun h => hvR (h.symm ▸ R.end_mem_support)
  let r : Piece G := ⟨a,x,P.append Q.reverse,hPQ,hax⟩
  let s : Piece G := ⟨v,b,Walk.cons hvt R,hR.cons hvR,hvb⟩
  refine ⟨r,s,?_,?_⟩
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq hPe e
    have h₂ := List.Perm.count_eq hRe e
    simp only [r,s,Walk.edges_append,Walk.edges_reverse,Walk.edges_cons,List.count_append,
      List.count_reverse,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega
  · apply List.perm_iff_count.mpr
    intro y
    have h₁ := List.Perm.count_eq hPv y
    have h₂ := List.Perm.count_eq hRv y
    simp only [r,s,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega

variable [Fintype V]

lemma no_clean_endpoint {L : List (Piece G)} (hL : Maximal L)
    {v x : V} (Q : G.Walk x v) (hx : G.Adj v x)
    (hC : (Walk.cons hx Q).IsCycle)
    (hunused : (edgeList L).Disjoint (Walk.cons hx Q).edges)
    (p : Piece G) (hp : p ∈ L) (hpv : v = p.src ∨ v = p.dst)
    (hclean : ∀ a, a ∈ p.walk.support → a ∈ Q.support → a = v) : False := by
  have hxu : (G \ coveredGraph L).Adj v x := by
    refine ⟨hx,?_⟩
    intro h
    exact hunused ((coveredGraph_adj L v x).mp h) (by simp)
  obtain ⟨t,M,hvt,ht,_,he,hv,hkeep,hmove⟩ := hL.1.rotate_endpoint_fan hxu
  obtain ⟨q,hq,hqt,hvq⟩ := hL.1.endpoint_path_avoids_of_not_touching ht
  obtain ⟨p',hp',hps,hsrc,hdst⟩ := hmove p hp
  have hpv' : v = p'.src ∨ v = p'.dst := by
    rcases hpv with hpv | hpv
    · exact Or.inl (hsrc hpv.symm).symm
    · exact Or.inr (hdst hpv.symm).symm
  have hclean' : ∀ a, a ∈ p'.walk.support → a ∈ Q.support → a = v :=
    fun a ha hb => hclean a (hps.mem_iff.mp ha) hb
  have hqp : q ≠ p' := by
    intro heq
    apply hvq
    rw [heq]
    rcases hpv' with h | h
    · exact h.symm ▸ p'.walk.start_mem_support
    · exact h.symm ▸ p'.walk.end_mem_support
  obtain ⟨N,hN⟩ := two_at_front hp' (hkeep q hq hvq) hqp
  have hedgeN := edgeList_perm hN
  have hendN := endpoints_perm hN
  obtain ⟨r,s,hrE,hrV⟩ := extend_clean_pair p' q Q
    ((Walk.cons_isCycle_iff Q hx).mp hC).1 hx hvt hpv' hqt hvq hclean'
  have hfinalE : (edgeList (r :: s :: N)).Perm
      (edgeList L ++ (Walk.cons hx Q).edges) := by
    apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq hedgeN e
    have h₃ := List.Perm.count_eq hrE e
    simp only [edgeList_cons,Walk.edges_cons,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ h₃ ⊢
    omega
  have hfinalV : (endpoints (r :: s :: N)).Perm (endpoints L) := by
    apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq hendN a
    have h₃ := List.Perm.count_eq hrV a
    simp only [endpoints_cons,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ h₃ ⊢
    omega
  exact hL.no_exchange hC.isTrail.edges_nodup (by simp) hunused hfinalE hfinalV

end FanAbsorption
end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.FanAbsorption.no_clean_endpoint
