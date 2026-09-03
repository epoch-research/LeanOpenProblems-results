import Submission.CartesianBoolRightCover
import Submission.RightCoverReduction
import Submission.RightFiberCover

/-! A second-right covering theorem under a star-triangle hypothesis.
The hypothesis is not asserted for arbitrary K4-free graphs. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoPrismSecondRight
open Erdos595Work Erdos595ArcAdjoint Erdos595MatchingBundle
open Erdos595CartesianBoolRight (prism)
variable {V : Type*} (H : SimpleGraph V)

abbrev Stars := {p : Biclique H // Star H p}
abbrev starGraph := (right H).induce {p | Star H p}

noncomputable def side (p : Stars H) : Bool := by
  classical
  exact if Left H p.val = {center H p.val p.property} then false else true

lemma side_left (p : Stars H) (hp : side H p = false) :
    Left H p.val = {center H p.val p.property} := by
  classical
  by_contra hn
  simp [side,hn] at hp

lemma side_right (p : Stars H) (hp : side H p = true) :
    Right H p.val = {center H p.val p.property} := by
  classical
  rcases center_spec H p.val p.property with h | h
  · simp [side,h] at hp
  · exact h

noncomputable def starHom : starGraph H →g prism H where
  toFun p := (center H p.val p.property,side H p)
  map_rel' := by
    intro p q hpq
    change (right H).Adj p.val q.val at hpq
    have hx := hpq.1.choose_spec
    have hy := hpq.2.choose_spec
    change hpq.1.choose ∈ Right H p.val ∧ hpq.1.choose ∈ Left H q.val at hx
    change hpq.2.choose ∈ Right H q.val ∧ hpq.2.choose ∈ Left H p.val at hy
    cases hp : side H p <;> cases hq : side H q
    · have hp' := side_left H p hp
      have hq' := side_left H q hq
      have he : hpq.2.choose = center H p.val p.property := by
        simpa only [hp',Set.mem_singleton_iff] using hy.2
      have hc : center H p.val p.property ∈ Right H q.val := he ▸ hy.1
      have hqc : center H q.val q.property ∈ Left H q.val := by rw [hq']; exact rfl
      exact Or.inl ⟨rfl,(q.val.property _ hqc _ hc).symm⟩
    · have hp' := side_left H p hp
      have hq' := side_right H q hq
      have he₁ : hpq.2.choose = center H p.val p.property := by
        simpa only [hp',Set.mem_singleton_iff] using hy.2
      have he₂ : hpq.2.choose = center H q.val q.property := by
        simpa only [hq',Set.mem_singleton_iff] using hy.1
      exact Or.inr ⟨he₁.symm.trans he₂,by simp⟩
    · have hp' := side_right H p hp
      have hq' := side_left H q hq
      have he₁ : hpq.1.choose = center H p.val p.property := by
        simpa only [hp',Set.mem_singleton_iff] using hx.1
      have he₂ : hpq.1.choose = center H q.val q.property := by
        simpa only [hq',Set.mem_singleton_iff] using hx.2
      exact Or.inr ⟨he₁.symm.trans he₂,by simp⟩
    · have hp' := side_right H p hp
      have hq' := side_right H q hq
      have he : hpq.1.choose = center H p.val p.property := by
        simpa only [hp',Set.mem_singleton_iff] using hx.1
      have hc : center H p.val p.property ∈ Left H q.val := he ▸ hx.2
      have hqc : center H q.val q.property ∈ Right H q.val := by rw [hq']; exact rfl
      exact Or.inl ⟨rfl,q.val.property _ hc _ hqc⟩

/-- Stars suffice at the first right stage; no uniqueness hypothesis is
needed once the star-triangle condition is given. -/
theorem cover_of_star_triangles
    (hs : ∀ {p q r : Biclique H}, (right H).Adj p q → (right H).Adj p r →
      (right H).Adj q r → Star H p)
    (hc : IsCountableUnionOfTriangleFree H) :
    IsCountableUnionOfTriangleFree (right (right H)) := by
  apply Erdos595RightCoverReduction.triangle_core (right H) {p | Star H p}
  · intro p q r hpq hpr hqr
    exact hs hpq hpr hqr
  · apply countable_union_of_hom (Erdos595RightFiber.rightHom (starHom H))
    apply Erdos595CartesianBoolRight.right_cover H
    exact Erdos595NoPrismRight.cover_of_star_triangles H hs hc

/-- Triangles of H may share vertices. They must be unique through edges,
and disjoint triangles must not be joined by a perfect matching. -/
theorem second_right_cover
    (hu : Erdos595ArcRoundTrip.UniqueTriangleEdge H)
    (hn : Erdos595NoPrismRight.NoPrism H) :
    IsCountableUnionOfTriangleFree (right (right H)) :=
  cover_of_star_triangles H (Erdos595NoPrismRight.triangle_star H hu hn)
    (Erdos595NoPrismRight.base_cover H hu)

#print axioms starHom
#print axioms cover_of_star_triangles
#print axioms second_right_cover
end Erdos595NoPrismSecondRight
