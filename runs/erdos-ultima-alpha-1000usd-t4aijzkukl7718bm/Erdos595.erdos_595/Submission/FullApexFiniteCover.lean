import Submission.FullApexSecondRightCover
import Submission.FiniteTransversalRightCover
import Submission.SecondConeCriterion

/-!
The K4-free second right adjoint of a full independent-apex family over a
triangle-free graph has a uniform THREE-piece triangle-free edge cover.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FullApexFiniteCover
open Erdos595ArcAdjoint Erdos595Work Erdos595CompleteFilterEdgeCover
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}

lemma pullback (f : G →g H) (hc : CoversWith H n) : CoversWith G n := by
  classical
  obtain ⟨K,hK,hcov⟩ := hc
  refine ⟨fun i => (K i).comap f,?_,?_⟩
  · intro i t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hK i _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show (K i).Adj (f a) (f b) ∧ (K i).Adj (f a) (f c) ∧
        (K i).Adj (f b) (f c) from ⟨hab,hac,hbc⟩))
  · intro a b hab
    exact hcov (f a) (f b) (f.map_adj hab)

open Erdos595FullApexSecondRight Erdos595Extension

theorem three_cover (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (h : (right (right (apexFamilyGraph G))).CliqueFree 4) :
    CoversWith (right (right (apexFamilyGraph G))) 3 :=
  pullback (rightMap (rightMap (collapse G)))
    (Erdos595FiniteTransversalRight.cone_three_cover_of_cliqueFree G
      ((second_cliqueFree_iff G hG).mp h))

theorem cliqueFree_iff_noFive (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (right (right (apexFamilyGraph G))).CliqueFree 4 ↔ Erdos595SecondConeRight.NoFive G :=
  (second_cliqueFree_iff G hG).trans (Erdos595SecondConeCriterion.cliqueFree_iff_noFive G)

#print axioms cliqueFree_iff_noFive
#print axioms pullback
#print axioms three_cover
end Erdos595FullApexFiniteCover
