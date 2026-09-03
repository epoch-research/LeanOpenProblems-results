import Submission.MixedPrivateBothCross

/-! Every locked cubic/quartic two-tail triangle admits a two-vertex Gallai reduction. -/
namespace Erdos583LockedMixedTriangleReductionDevelopment
open SimpleGraph Erdos583Work
open Erdos583TriangleTailRootTemplatesDevelopment
open Erdos583MixedPrivateTipDevelopment Erdos583MixedPrivateFreshDevelopment
open Erdos583MixedPrivateBothCrossDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma locked_mixed_triangle_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y s t c : Fin n}
    (F : Frame G r x y s t) (hxs : G.Adj x s) (hxt : G.Adj x t) (hyc : G.Adj y c)
    (hcr : c ≠ r) (hcx : c ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=s ∨ z=t)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  let K := puncture G ({x,y} : Set (Fin n))
  have hrsK : K.Adj r s := ⟨F.rs,by simp [F.rx.ne,F.ry.ne],by simp [F.sx,F.sy]⟩
  have hstK : K.Adj s t := ⟨F.st,by simp [F.sx,F.sy],by simp [F.tx,F.ty]⟩
  have hrtK : K.Reachable r t := hrsK.reachable.trans hstK.reachable
  have hNx' : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=t ∨ z=s := by
    intro z hz
    rcases hNx z hz with hh | hh | hh | hh <;> tauto
  by_cases hcs : c=s
  · subst c
    exact mixed_private_tip_reduction hsmall hG F.rx F.xy F.ry hxs hxt hyc
      F.rs.ne.symm F.tr F.ty F.st.ne hNx hNy hrsK.reachable hrtK
  by_cases hct : c=t
  · subst c
    exact mixed_private_tip_reduction hsmall hG F.rx F.xy F.ry hxt hxs hyc
      F.tr F.rs.ne.symm F.sy F.st.ne.symm hNx' hNy hrtK hrsK.reachable
  by_cases hsc : G.Adj s c
  · by_cases htc : G.Adj t c
    · exact mixed_private_both_cross_reduction hsmall hG F hxs hxt hyc hcr hcx hcs hct hsc htc hNx hNy
    · exact mixed_private_fresh_cross_reduction hsmall hG F.rx F.xy F.ry hxt hxs hyc
        F.tr F.rs.ne.symm F.ty F.sy F.st.ne.symm hcr hcx (Ne.symm hct) hNx' hNy hrtK hrsK.reachable htc
  · exact mixed_private_fresh_cross_reduction hsmall hG F.rx F.xy F.ry hxs hxt hyc
      F.rs.ne.symm F.tr F.sy F.ty F.st.ne hcr hcx (Ne.symm hcs) hNx hNy hrsK.reachable hrtK hsc

end Erdos583LockedMixedTriangleReductionDevelopment
