import Submission.ThinMarkedSecondRight

/-!
The thin-marked argument extends to marked neighborhoods whose every edge
is dominating. For a triangle-free neighborhood this is the complete
bipartite condition, and in particular it includes stars of arbitrary size.
The full second right adjoint has two triangle-free edge pieces.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595DominatedMarkedSecondRight
open Erdos595ArcAdjoint Erdos595MatchingBundle Erdos595ExactTransversalRight
open Erdos595ThinMarkedSecondRight
variable {V : Type*} (H : SimpleGraph V) (m : V → Bool)

/-- Every edge of the neighborhood of a marked vertex dominates that
neighborhood. No condition is imposed if the neighborhood has no edge. -/
def Dominated : Prop :=
  ∀ a b c, m a = true → H.Adj a b → H.Adj a c → H.Adj b c →
    ∀ d, H.Adj a d → H.Adj b d ∨ H.Adj c d

lemma dominated_of_thin (ht : Thin H m) : Dominated H m := by
  intro a b c ha hab hac hbc d had
  rcases ht a b c ha hab hac hbc d had with rfl | rfl
  · exact Or.inr hbc.symm
  · exact Or.inl hbc

variable (hm : ExactTransversal H m) (hd : Dominated H m)
variable {p q r : Biclique H} (s : Six H p q r)

include hm hd in
lemma side_of_mark (hx : m s.x = true) : MarkedSide H m p ∨ MarkedSide H m q := by
  have ht := s.tri H
  obtain ⟨hy,hz⟩ := other_marks H m hm ht.1 ht.2.1 ht.2.2 hx
  have hxx' : H.Adj s.x s.x' := q.property _ s.hx.2 _ s.hx'.1
  rcases hd s.x s.y s.z hx ht.1 ht.2.1 ht.2.2 s.x' hxx' with he | he
  · have hx' : m s.x' = false := (other_marks H m hm ht.1 hxx' he hx).2
    right
    left
    refine ⟨⟨s.x,s.hx.2⟩,?_⟩
    intro v hv
    have hyv := (q.property _ hv _ s.hy.1).symm
    have hxv := (q.property _ hv _ s.hx'.1).symm
    have h := hm s.y s.x' v he hyv hxv
    cases hv' : m v <;> simp_all
  · have hx' : m s.x' = false := (other_marks H m hm ht.2.1 hxx' he hx).2
    left
    right
    refine ⟨⟨s.x,s.hx.1⟩,?_⟩
    intro v hv
    have hzv := p.property _ s.hz.2 _ hv
    have hxv := p.property _ s.hx'.2 _ hv
    have h := hm s.z s.x' v he hzv hxv
    cases hv' : m v <;> simp_all

include hm hd s in
lemma exists_markedSide : MarkedSide H m p ∨ MarkedSide H m q ∨ MarkedSide H m r := by
  have ht := s.tri H
  have he := hm s.x s.y s.z ht.1 ht.2.1 ht.2.2
  have hx : m s.x = true ∨ m s.y = true ∨ m s.z = true := by
    cases h₀ : m s.x <;> cases h₁ : m s.y <;> cases h₂ : m s.z <;> simp_all
  rcases hx with hx | hx | hx
  · exact (side_of_mark H m hm hd s hx).imp_right Or.inl
  · exact Or.inr (side_of_mark H m hm hd (rotate H s) hx)
  · rcases side_of_mark H m hm hd (rotate H (rotate H s)) hx with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

include hm hd in
theorem lift_exact : ExactTransversal (right H) (liftMark H m) := by
  classical
  intro p q r hpq hpr hqr
  let s := six H hpq hpr hqr
  have he := exists_markedSide H m hm hd s
  have hpq' := not_two_markedSides H m hm s
  have hqr' := not_two_markedSides H m hm (rotate H s)
  have hrp' := not_two_markedSides H m hm (rotate H (rotate H s))
  by_cases hp : MarkedSide H m p <;> by_cases hq : MarkedSide H m q <;>
    by_cases hr : MarkedSide H m r <;> simp_all [liftMark]

include hm hd in
theorem second_right_two_cover :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right H)) 2 :=
  two_cover (right H) (liftMark H m) (lift_exact H m hm hd)

#print axioms lift_exact
#print axioms second_right_two_cover
end Erdos595DominatedMarkedSecondRight
