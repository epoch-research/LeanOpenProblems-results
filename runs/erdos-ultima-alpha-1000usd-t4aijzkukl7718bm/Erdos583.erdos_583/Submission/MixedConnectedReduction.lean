import Submission.MixedConnectedCross

/-! A present quartic shortcut and connected punctured support suffice for the mixed reduction. -/
namespace Erdos583MixedConnectedReductionDevelopment
open SimpleGraph Erdos583Work
open Erdos583MixedPrivateTipDevelopment Erdos583MixedPrivateFreshDevelopment
open Erdos583MixedConnectedCrossDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_connected_shortcut_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y a b c : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hyc : G.Adj y c)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (habG : G.Adj a b) (hcr : c ≠ r) (hcx : c ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c)
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (hrK : r ∈ (puncture G ({x,y} : Set (Fin n))).support) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  have habK : (puncture G ({x,y} : Set (Fin n))).Adj a b :=
    ⟨habG,by simp [hxa.ne.symm,hay],by simp [hxb.ne.symm,hby]⟩
  have hra := hK r hrK a ⟨b,habK⟩
  have hrb := hK r hrK b ⟨a,habK.symm⟩
  have hNx' : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=b ∨ z=a := by
    intro z hz
    rcases hNx z hz with hh | hh | hh | hh <;> tauto
  by_cases hca : c=a
  · subst c
    exact mixed_private_tip_reduction hsmall hG hrx hxy hry hxa hxb hyc har hbr hby habG.ne hNx hNy hra hrb
  by_cases hcb : c=b
  · subst c
    exact mixed_private_tip_reduction hsmall hG hrx hxy hry hxb hxa hyc hbr har hay habG.ne.symm hNx' hNy hrb hra
  by_cases hac : G.Adj a c
  · by_cases hbc : G.Adj b c
    · exact mixed_connected_both_cross_reduction hsmall hrx hxy hry hxa hxb hyc har hbr hay hby habG
        hcr hcx hca hcb hac hbc hNx hNy hK
    · exact mixed_private_fresh_cross_reduction hsmall hG hrx hxy hry hxb hxa hyc
        hbr har hby hay habG.ne.symm hcr hcx (Ne.symm hcb) hNx' hNy hrb hra hbc
  · exact mixed_private_fresh_cross_reduction hsmall hG hrx hxy hry hxa hxb hyc
      har hbr hay hby habG.ne hcr hcx (Ne.symm hca) hNx hNy hra hrb hac

end Erdos583MixedConnectedReductionDevelopment
