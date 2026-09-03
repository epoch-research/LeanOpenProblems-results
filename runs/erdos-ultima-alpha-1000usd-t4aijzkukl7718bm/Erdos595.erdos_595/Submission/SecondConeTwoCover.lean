import Submission.SecondConeCliqueCover
import Submission.ExactTransversalRightCover

/-! The K4-free second right adjoint of a single cone has TWO triangle-free
edge pieces. This improves the earlier three-piece exclusion, not Erdos 595. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondConeTwo
open Erdos595Work Erdos595ArcAdjoint Erdos595SecondConeRight
open Erdos595ExactTransversalRight Erdos595CompleteFilterEdgeCover
variable {V : Type*} (G : SimpleGraph V)

/-- Two pure bicliques can be adjacent, but their edge lies in no triangle.
There is no hypothesis on the base graph in this assertion. -/
lemma not_two_pure {p q r : P G} (hp : Pure G p) (hq : Pure G q)
    (hpq : (right (coneGraph G)).Adj p q)
    (hpr : (right (coneGraph G)).Adj p r)
    (hqr : (right (coneGraph G)).Adj q r) : False := by
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · obtain ⟨x,hxp,hxq⟩ := hpq.1
    have hx : x = none := by simpa only [hq,Set.mem_singleton_iff] using hxq
    subst x
    exact p.property none (by simp [hp]) none hxp
  · obtain ⟨x,hxr,hxp⟩ := hpr.2
    obtain ⟨y,hyq,hyr⟩ := hqr.1
    have hx : x = none := by simpa only [hp,Set.mem_singleton_iff] using hxp
    have hy : y = none := by simpa only [hq,Set.mem_singleton_iff] using hyq
    subst x
    subst y
    exact r.property none hyr none hxr
  · obtain ⟨x,hxp,hxr⟩ := hpr.1
    obtain ⟨y,hyr,hyq⟩ := hqr.2
    have hx : x = none := by simpa only [hp,Set.mem_singleton_iff] using hxp
    have hy : y = none := by simpa only [hq,Set.mem_singleton_iff] using hyq
    subst x
    subst y
    exact r.property none hxr none hyr
  · obtain ⟨x,hxp,hxq⟩ := hpq.1
    have hx : x = none := by simpa only [hp,Set.mem_singleton_iff] using hxp
    subst x
    exact q.property none hxq none (by simp [hq])

/-- Under NoFive, the pure bicliques meet every triangle in exactly one
vertex; they need not be independent. -/
theorem exact_pure (h : NoFive G) :
    ExactTransversal (right (coneGraph G)) (fun p => @decide (Pure G p) (Classical.propDecidable _)) := by
  classical
  intro p q r hpq hpr hqr
  have hs : Pure G p ∨ Pure G q ∨ Pure G r := by
    by_contra hn
    simp only [not_or] at hn
    exact pure_transversal G h _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show ((right (coneGraph G)).induce {p | ¬Pure G p}).Adj ⟨p,hn.1⟩ ⟨q,hn.2.1⟩ ∧
        ((right (coneGraph G)).induce {p | ¬Pure G p}).Adj ⟨p,hn.1⟩ ⟨r,hn.2.2⟩ ∧
        ((right (coneGraph G)).induce {p | ¬Pure G p}).Adj ⟨q,hn.2.1⟩ ⟨r,hn.2.2⟩ from
        ⟨hpq,hpr,hqr⟩))
  have hn₁ : ¬(Pure G p ∧ Pure G q) := fun hh => not_two_pure G hh.1 hh.2 hpq hpr hqr
  have hn₂ : ¬(Pure G p ∧ Pure G r) := fun hh => not_two_pure G hh.1 hh.2 hpr hpq hqr.symm
  have hn₃ : ¬(Pure G q ∧ Pure G r) := fun hh => not_two_pure G hh.1 hh.2 hqr hpq.symm hpr.symm
  by_cases hp : Pure G p <;> by_cases hq : Pure G q <;> by_cases hr : Pure G r <;>
    simp_all

/-- No size restriction on the cone base is needed. -/
theorem two_cover (h : NoFive G) : CoversWith (right (right (coneGraph G))) 2 :=
  Erdos595ExactTransversalRight.two_cover (right (coneGraph G)) _ (exact_pure G h)

/-- The full second right target being K4-free forces the NoFive hypothesis. -/
theorem two_cover_of_cliqueFree (h : (right (right (coneGraph G))).CliqueFree 4) :
    CoversWith (right (right (coneGraph G))) 2 :=
  two_cover G (Erdos595SecondConeClique.noFive_of_cliqueFree G h)

#print axioms not_two_pure
#print axioms exact_pure
#print axioms two_cover_of_cliqueFree
end Erdos595SecondConeTwo
