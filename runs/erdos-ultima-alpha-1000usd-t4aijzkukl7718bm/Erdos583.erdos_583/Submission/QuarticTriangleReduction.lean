import Submission.QuarticTwins
import Submission.QuarticPairCross

/-! Quartic nonroot pairs are reducible when deleting their triangle leaves connected support. -/
namespace Erdos583QuarticTriangleReductionDevelopment
open SimpleGraph Erdos583Work Erdos583QuarticPairProxyDevelopment
open Erdos583QuarticTwinsDevelopment Erdos583PunctureConnectivityDevelopment
open Erdos583TwoExistingShortcutsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_quartic_triangle_data {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y a b c d : Fin n} (F : QuarticData G r x y a b c d)
    (hJ : SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n)))))
    (hrJ : r ∈ (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n)))).support) : False := by
  classical
  by_cases hpairs : s(a,b)=s(c,d)
  · rcases Sym2.eq_iff.mp hpairs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact failure_no_quartic_twins_data hsmall hG hfail F
    · exact failure_no_quartic_twins_data hsmall hG hfail F.swapY
  let C : Set (Sym2 (Fin n)) := {s(r,x),s(x,y),s(r,y)}
  let J := G.deleteEdges C
  have hxaJ : J.Adj x a := deleteEdges_adj.mpr ⟨F.xa,by
    simp [C,F.rx.ne.symm,F.xy.ne,F.ar,F.ay]⟩
  have hxbJ : J.Adj x b := deleteEdges_adj.mpr ⟨F.xb,by
    simp [C,F.rx.ne.symm,F.xy.ne,F.br,F.byy]⟩
  have hycJ : J.Adj y c := deleteEdges_adj.mpr ⟨F.yc,by
    simp [C,F.ry.ne.symm,F.xy.ne.symm,F.cr,F.cx]⟩
  have hydJ : J.Adj y d := deleteEdges_adj.mpr ⟨F.yd,by
    simp [C,F.ry.ne.symm,F.xy.ne.symm,F.dr,F.dx]⟩
  have hNxJ : ∀ z, J.Adj x z → z=a ∨ z=b := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases F.Nx z hz with rfl | rfl | h | h
    · exact (hnz (Or.inl Sym2.eq_swap)).elim
    · exact (hnz (Or.inr (Or.inl rfl))).elim
    · exact Or.inl h
    · exact Or.inr h
  have hNyJ : ∀ z, J.Adj y z → z=c ∨ z=d := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases F.Ny z hz with rfl | rfl | h | h
    · exact (hnz (Or.inr (Or.inr Sym2.eq_swap))).elim
    · exact (hnz (Or.inr (Or.inl Sym2.eq_swap))).elim
    · exact Or.inl h
    · exact Or.inr h
  have hdis : Disjoint C J.edgeSet := by
    rw [edgeSet_deleteEdges]
    exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
  have hcover : G.edgeSet=J.edgeSet ∪ C := by
    rw [edgeSet_deleteEdges]
    apply (Set.diff_union_of_subset _).symm
    rintro e (rfl|rfl|rfl)
    · exact F.rx
    · exact F.xy
    · exact F.ry
  obtain ⟨habJ,hcdJ⟩ := failure_two_shortcuts_present hsmall hG hfail (deleteEdges_le C) hJ
    F.rx F.xy F.ry hdis hcover hrJ hxaJ hxbJ hycJ hydJ F.ab F.cd F.ar F.br F.ay F.byy
    F.cr F.dr F.cx F.dx hNxJ hNyJ hpairs
  have hX := puncture_degree_two_connected_of_shortcut hJ hxaJ hxbJ habJ hNxJ
  have hycX : (puncture J ({x} : Set (Fin n))).Adj y c :=
    ⟨hycJ,F.xy.ne.symm,F.cx⟩
  have hydX : (puncture J ({x} : Set (Fin n))).Adj y d :=
    ⟨hydJ,F.xy.ne.symm,F.dx⟩
  have hcdX : (puncture J ({x} : Set (Fin n))).Adj c d := ⟨hcdJ,F.cx,F.dx⟩
  have hK := puncture_degree_two_connected_of_shortcut hX hycX hydX hcdX
    (fun z hz ↦ hNyJ z hz.1)
  rw [show puncture (puncture J ({x} : Set (Fin n))) {y}=puncture G ({x,y} : Set (Fin n)) from
    puncture_pair_eq_of_triangle_deletion G r x y] at hK
  exact hfail (Erdos583QuarticPairCrossDevelopment.QuarticData.distinct_pairs_reduction
    hsmall F hK (deleteEdges_le C habJ) (deleteEdges_le C hcdJ) hpairs)

end Erdos583QuarticTriangleReductionDevelopment
