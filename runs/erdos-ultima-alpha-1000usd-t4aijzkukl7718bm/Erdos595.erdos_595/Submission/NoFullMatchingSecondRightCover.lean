import Submission.FullMatchingBundleRightCover
import Submission.ExactTransversalRightCover

/-! Without a full three-edge cross-fiber matching, every triangle of the
first right adjoint consists of stars. This yields a TWO-piece cover of the
second right adjoint. Full matching pairs remain an essential unresolved case. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoFullMatching
open Erdos595ArcAdjoint Erdos595MatchingBundle Erdos595FullMatchingBundle
variable {V I : Type*} (H : SimpleGraph V) (π : V → I) (κ : V → Fin 3)

/-- Three disjoint cross edges between two different fibers. Under Core,
these use all three vertices of each fiber, hence constitute a full matching. -/
def FullPair (i j : I) : Prop :=
  i ≠ j ∧ ∃ a b : Fin 3 → V, Function.Injective a ∧ Function.Injective b ∧
    ∀ k, π (a k) = i ∧ π (b k) = j ∧ H.Adj (a k) (b k)

variable (h : Core H π κ)

include h in
/-- The two directed witness cycles of a non-star triangle force a full pair. -/
theorem nonstar_fullPair {p q r : Biclique H} (s : Six H p q r) (hp : ¬Star H p) :
    FullPair H π (π s.x) (π s.x') := by
  have hf := Erdos595FullMatchingBundle.fibers H π κ h s
  have ht := s.tri H
  have ht' := s.tri' H
  refine ⟨Erdos595FullMatchingBundle.different_fibers H π κ h s hp,
    ![s.x,s.y,s.z],![s.x',s.y',s.z'],?_,?_,?_⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;> dsimp at he ⊢ <;>
      simp_all
  · intro i j he
    fin_cases i <;> fin_cases j <;> dsimp at he ⊢ <;>
      simp_all
  · intro k
    fin_cases k
    · exact ⟨rfl,rfl,q.property _ s.hx.2 _ s.hx'.1⟩
    · exact ⟨hf.1.1.symm,hf.2.1.symm,r.property _ s.hy.2 _ s.hy'.1⟩
    · exact ⟨hf.1.2.symm,hf.2.2.symm,p.property _ s.hz.2 _ s.hz'.1⟩

variable (hn : ∀ i j, ¬FullPair H π i j)

include h hn in
lemma triangle_star {p q r : Biclique H} (hpq : (right H).Adj p q)
    (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) : Star H p := by
  by_contra hp
  exact hn _ _ (nonstar_fullPair H π κ h (six H hpq hpr hqr) hp)

noncomputable def color (p : Biclique H) : Fin 3 := by
  classical
  exact if hp : Star H p then κ (center H p hp) else 0

include h hn in
lemma color_ne {p q r : Biclique H} (hpq : (right H).Adj p q)
    (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) :
    color H κ p ≠ color H κ q := by
  classical
  have hp := triangle_star H π κ h hn hpq hpr hqr
  have hq := triangle_star H π κ h hn hpq.symm hqr hpr
  let s := six H hpq hpr hqr
  have hf := Erdos595FullMatchingBundle.fibers H π κ h s
  have hpf := center_fiber H π hp s.hz.2 s.hx.1 hf.1.2.symm
  have hqf := center_fiber H π hq s.hx.2 s.hy.1 hf.1.1
  have hc := Erdos595FullMatchingBundle.coord_ne H π κ h (centers_ne H s hp hq)
    ((hpf.trans hf.1.2.symm).trans hqf.symm)
  simpa only [color,dif_pos hp,dif_pos hq] using hc

include h hn in
/-- All first-right triangles are rainbow for three vertex labels. -/
theorem right_rainbow {p q r : Biclique H} (hpq : (right H).Adj p q)
    (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) :
    color H κ p ≠ color H κ q ∧ color H κ p ≠ color H κ r ∧ color H κ q ≠ color H κ r :=
  ⟨color_ne H π κ h hn hpq hpr hqr,color_ne H π κ h hn hpr hpq hqr.symm,
    color_ne H π κ h hn hqr hpq.symm hpr.symm⟩

include h hn in
/-- Arbitrarily many partial two-edge matchings are permitted; only full
three-edge cross matchings are excluded. There is no index-clique hypothesis. -/
theorem second_right_two_cover :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right H)) 2 :=
  Erdos595ExactTransversalRight.two_cover_of_rainbow (right H) (color H κ)
    (fun _ _ _ => right_rainbow H π κ h hn)

include h hn in
theorem second_right_cover : Erdos595Work.IsCountableUnionOfTriangleFree (right (right H)) :=
  (show Erdos595BadEdge.FiniteCover (right (right H)) from
    ⟨2,second_right_two_cover H π κ h hn⟩).countable

#print axioms nonstar_fullPair
#print axioms right_rainbow
#print axioms second_right_two_cover
#print axioms second_right_cover
end Erdos595NoFullMatching
