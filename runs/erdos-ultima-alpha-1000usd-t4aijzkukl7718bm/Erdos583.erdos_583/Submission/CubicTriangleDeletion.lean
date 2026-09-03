import Submission.ShortTriangleCubicCut

/-! Deleting the two leaf vertices left by a cubic triangle preserves external links. -/
namespace Erdos583CubicTriangleDeletionDevelopment
open SimpleGraph Erdos583Work Erdos583LeafPunctureDevelopment
open Erdos583PunctureConnectivityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma puncture_leaf_reachable {V : Type*} {G : SimpleGraph V} {x a u v : V}
    (hNx : ∀ z, G.Adj x z → z=a) (hux : u ≠ x) (hvx : v ≠ x) (h : G.Reachable u v) :
    (puncture G ({x} : Set V)).Reachable u v := by
  classical
  let f (z : V) := if z=x then a else z
  have hedge (s t : V) (hst : G.Adj s t) : (puncture G ({x} : Set V)).Reachable (f s) (f t) := by
    by_cases hs : s=x
    · subst s
      have ht := hst.ne.symm
      simp only [f,if_pos rfl,if_neg ht]
      rw [hNx t hst]
    by_cases ht : t=x
    · subst t
      simp only [f,if_neg hs,if_pos rfl]
      rw [hNx s hst.symm]
    simp only [f,if_neg hs,if_neg ht]
    exact (show (puncture G ({x} : Set V)).Adj s t from ⟨hst,hs,ht⟩).reachable
  simpa only [f,if_neg hux,if_neg hvx] using reachable_map_to_reachable f hedge h

lemma cubic_triangle_deletion_links {V : Type*} {G : SimpleGraph V} {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hJ : SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))))
    (hrJ : r ∈ (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))).support) :
    SupportConnected (puncture G ({x,y} : Set V)) ∧
      (puncture G ({x,y} : Set V)).Reachable r a ∧ (puncture G ({x,y} : Set V)).Reachable r b := by
  let C : Set (Sym2 V) := {s(r,x),s(x,y),s(r,y)}
  let J := G.deleteEdges C
  have hxaJ : J.Adj x a := deleteEdges_adj.mpr ⟨hxa,by simp [C,hrx.ne.symm,hxy.ne,har,hay]⟩
  have hybJ : J.Adj y b := deleteEdges_adj.mpr ⟨hyb,by simp [C,hry.ne.symm,hxy.ne.symm,hbr,hbx]⟩
  have hNxJ : ∀ z, J.Adj x z → z=a := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNx z hz with rfl | rfl | h
    · exact (hnz (Or.inl Sym2.eq_swap)).elim
    · exact (hnz (Or.inr (Or.inl rfl))).elim
    · exact h
  have hNyJ : ∀ z, J.Adj y z → z=b := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNy z hz with rfl | rfl | h
    · exact (hnz (Or.inr (Or.inr Sym2.eq_swap))).elim
    · exact (hnz (Or.inr (Or.inl Sym2.eq_swap))).elim
    · exact h
  have hNyX : ∀ z, (puncture J ({x} : Set V)).Adj y z → z=b := fun z hz ↦ hNyJ z hz.1
  have hK := puncture_leaf_connected (puncture_leaf_connected hJ hNxJ) hNyX
  have hra := puncture_leaf_reachable hNyX hry.ne hay
    (puncture_leaf_reachable hNxJ hrx.ne hxa.ne.symm (hJ r hrJ a ⟨x,hxaJ.symm⟩))
  have hrb := puncture_leaf_reachable hNyX hry.ne hyb.ne.symm
    (puncture_leaf_reachable hNxJ hrx.ne hbx (hJ r hrJ b ⟨y,hybJ.symm⟩))
  have he : puncture (puncture J ({x} : Set V)) {y}=puncture G ({x,y} : Set V) :=
    puncture_pair_eq_of_triangle_deletion G r x y
  rw [he] at hK hra hrb
  exact ⟨hK,hra,hrb⟩

end Erdos583CubicTriangleDeletionDevelopment
