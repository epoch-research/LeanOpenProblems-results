import Submission.ExactTransversalRightCover
import Submission.MatchingBundleRightCover

/-!
If every triangle has exactly one marked vertex and that vertex has only
its two triangle neighbors, an exact-one marking lifts to the first right
adjoint. Consequently the second right adjoint has a two-piece edge cover.
This excludes private edge-ear constructions; it does not settle Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595ThinMarkedSecondRight
open Erdos595ArcAdjoint Erdos595MatchingBundle Erdos595ExactTransversalRight
variable {V : Type*} (H : SimpleGraph V) (m : V → Bool)

/-- Each marked vertex in a triangle has no further neighbors. -/
def Thin : Prop :=
  ∀ a b c, m a = true → H.Adj a b → H.Adj a c → H.Adj b c →
    ∀ d, H.Adj a d → d = b ∨ d = c

def MarkedSide (p : Biclique H) : Prop :=
  ((Left H p).Nonempty ∧ ∀ a ∈ Left H p, m a = true) ∨
  ((Right H p).Nonempty ∧ ∀ a ∈ Right H p, m a = true)

noncomputable def liftMark (p : Biclique H) : Bool := by
  classical
  exact decide (MarkedSide H m p)

variable (hm : ExactTransversal H m) (hthin : Thin H m)
variable {p q r : Biclique H} (s : Six H p q r)

include hm in
lemma other_marks {a b c : V} (hab : H.Adj a b) (hac : H.Adj a c)
    (hbc : H.Adj b c) (ha : m a = true) : m b = false ∧ m c = false := by
  have he := hm a b c hab hac hbc
  cases hb : m b <;> cases hc : m c <;> simp_all

include hm hthin in
lemma side_of_mark (hx : m s.x = true) : MarkedSide H m p ∨ MarkedSide H m q := by
  have ht := s.tri H
  obtain ⟨hy,hz⟩ := other_marks H m hm ht.1 ht.2.1 ht.2.2 hx
  have hxx' : H.Adj s.x s.x' := q.property _ s.hx.2 _ s.hx'.1
  rcases hthin s.x s.y s.z hx ht.1 ht.2.1 ht.2.2 s.x' hxx' with he | he
  · left
    right
    refine ⟨⟨s.x,s.hx.1⟩,?_⟩
    intro v hv
    have hyv : H.Adj s.y v := p.property _ (he ▸ s.hx'.2) _ hv
    have hzv : H.Adj s.z v := p.property _ s.hz.2 _ hv
    have h := hm s.y s.z v ht.2.2 hyv hzv
    cases hv' : m v <;> simp_all
  · right
    left
    refine ⟨⟨s.x,s.hx.2⟩,?_⟩
    intro v hv
    have hzy : H.Adj s.z s.y := ht.2.2.symm
    have hzv : H.Adj s.z v := (q.property _ hv _ (he ▸ s.hx'.1)).symm
    have hyv : H.Adj s.y v := (q.property _ hv _ s.hy.1).symm
    have h := hm s.z s.y v hzy hzv hyv
    cases hv' : m v <;> simp_all

def rotate : Six H q r p where
  x := s.y
  y := s.z
  z := s.x
  x' := s.y'
  y' := s.z'
  z' := s.x'
  hx := s.hy
  hy := s.hz
  hz := s.hx
  hx' := s.hy'
  hy' := s.hz'
  hz' := s.hx'

include hm hthin s in
lemma exists_markedSide : MarkedSide H m p ∨ MarkedSide H m q ∨ MarkedSide H m r := by
  have ht := s.tri H
  have he := hm s.x s.y s.z ht.1 ht.2.1 ht.2.2
  have hx : m s.x = true ∨ m s.y = true ∨ m s.z = true := by
    cases h₀ : m s.x <;> cases h₁ : m s.y <;> cases h₂ : m s.z <;> simp_all
  rcases hx with hx | hx | hx
  · exact (side_of_mark H m hm hthin s hx).imp_right Or.inl
  · exact Or.inr (side_of_mark H m hm hthin (rotate H s) hx)
  · rcases side_of_mark H m hm hthin (rotate H (rotate H s)) hx with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

include hm s in
lemma not_two_markedSides : ¬(MarkedSide H m p ∧ MarkedSide H m q) := by
  rintro ⟨hp,hq⟩
  have ht := s.tri H
  have ht' := s.tri' H
  have hf := hm s.x s.y s.z ht.1 ht.2.1 ht.2.2
  have hb := hm s.x' s.y' s.z' ht'.1 ht'.2.1 ht'.2.2
  rcases hp with ⟨_,hp⟩ | ⟨_,hp⟩ <;> rcases hq with ⟨_,hq⟩ | ⟨_,hq⟩
  · rw [hp _ s.hz.2,hq _ s.hx.2] at hf
    simp only [Bool.toNat_true] at hf
    omega
  · rw [hp _ s.hz.2,hq _ s.hy.1] at hf
    simp only [Bool.toNat_true] at hf
    omega
  · rw [hp _ s.hz'.1,hq _ s.hy'.2] at hb
    simp only [Bool.toNat_true] at hb
    omega
  · rw [hp _ s.hx.1,hq _ s.hy.1] at hf
    simp only [Bool.toNat_true] at hf
    omega

include hm hthin in
/-- Marking nonempty monochromatically marked sides gives exactly one
marked biclique in every right-adjoint triangle. -/
theorem lift_exact : ExactTransversal (right H) (liftMark H m) := by
  classical
  intro p q r hpq hpr hqr
  let s := six H hpq hpr hqr
  have he := exists_markedSide H m hm hthin s
  have hpq' := not_two_markedSides H m hm s
  have hqr' := not_two_markedSides H m hm (rotate H s)
  have hrp' := not_two_markedSides H m hm (rotate H (rotate H s))
  by_cases hp : MarkedSide H m p <;> by_cases hq : MarkedSide H m q <;>
    by_cases hr : MarkedSide H m r <;> simp_all [liftMark]

include hm hthin in
theorem second_right_two_cover :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right H)) 2 :=
  two_cover (right H) (liftMark H m) (lift_exact H m hm hthin)

#print axioms lift_exact
#print axioms second_right_two_cover
end Erdos595ThinMarkedSecondRight
