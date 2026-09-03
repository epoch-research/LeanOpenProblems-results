import Submission.ExistingShortcutTriangle

/-! Both external shortcut edges are forced for a degree-four triangular pair. -/
namespace Erdos583TwoExistingShortcutsDevelopment
open SimpleGraph Erdos583Work
open Erdos583ExistingShortcutTriangleDevelopment Erdos583DoubleSmoothTriangleDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_two_shortcuts_present {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) (hF : SupportConnected F) {r x y a b c d : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ {s(r,x),s(x,y),s(r,y)}) (hrF : r ∈ F.support)
    (hxa : F.Adj x a) (hxb : F.Adj x b) (hyc : F.Adj y c) (hyd : F.Adj y d)
    (hab : a ≠ b) (hcd : c ≠ d) (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (hcr : c ≠ r) (hdr : d ≠ r) (hcx : c ≠ x) (hdx : d ≠ x)
    (hNx : ∀ z, F.Adj x z → z=a ∨ z=b) (hNy : ∀ z, F.Adj y z → z=c ∨ z=d)
    (hpairs : s(a,b) ≠ s(c,d)) : F.Adj a b ∧ F.Adj c d := by
  classical
  have hswap : ({s(r,y),s(y,x),s(r,x)} : Set (Sym2 (Fin n)))={s(r,x),s(x,y),s(r,y)} := by
    ext e
    simp [Sym2.eq_swap,or_comm,or_left_comm]
  by_cases ha : F.Adj a b
  · refine ⟨ha,?_⟩
    by_contra hc
    exact failure_no_one_existing_one_fresh_shortcut hsmall hG hfail hFG hF hrx hxy hry hdis hcover
      hrF hxa hxb ha har hbr hay hby hNx hyc hyd hcd hNy hc
  · by_cases hc : F.Adj c d
    · exact (failure_no_one_existing_one_fresh_shortcut hsmall hG hfail hFG hF hry hxy.symm hrx
        (by rwa [hswap]) (by rwa [hswap]) hrF hyc hyd hc hcr hdr hcx hdx hNy hxa hxb hab hNx ha).elim
    · exact (hfail (two_fresh_shortcuts_triangle_reduction hsmall hFG hF hrx hxy hry hdis hcover
        hxa hxb hyc hyd hab hcd hay hby hNx hNy ha hc hpairs)).elim

end Erdos583TwoExistingShortcutsDevelopment
