import Submission.NegativeInner

/-!
A local order criterion for triangle-free edge covers. Each homogeneous
rooted neighborhood is oriented by labels with no directed two-edge path.
This is auxiliary work, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595LocalInterval
open Erdos595Work
variable {V C K : Type*} [LinearOrder V] [LinearOrder K] [Countable C]

structure MonoTri (G : SimpleGraph V) (col : V → V → C) (a b c : V) : Prop where
  root_left : a < b
  root_right : a < c
  left_adj : G.Adj a b
  right_adj : G.Adj a c
  cross_adj : G.Adj b c
  color_left : col a b = col a c
  color_cross : col a b = col (min b c) (max b c)

lemma MonoTri.symm {G : SimpleGraph V} {col : V → V → C} {a b c : V}
    (h : MonoTri G col a b c) : MonoTri G col a c b where
  root_left := h.root_right
  root_right := h.root_left
  left_adj := h.right_adj
  right_adj := h.left_adj
  cross_adj := h.cross_adj.symm
  color_left := h.color_left.symm
  color_cross := by simpa only [min_comm,max_comm] using h.color_left.symm.trans h.color_cross

/-- A finite type palette and one local orientation bit suffice under the
stated no-monotone-two-path condition. -/
theorem countable_cover (G : SimpleGraph V) (col : V → V → C) (lab : V → V → K)
    (hsep : ∀ a b c, MonoTri G col a b c → lab a b ≠ lab a c)
    (hno : ∀ a b c d, MonoTri G col a b c → MonoTri G col a c d →
      lab a b < lab a c → lab a c < lab a d → False) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let HasLower (a b : V) := ∃ d, MonoTri G col a d b ∧ lab a d < lab a b
  let code (a b : V) := (col a b,decide (HasLower a b))
  apply Erdos595NegativeInner.cover_of_ordered_patterns G code
  intro a b c hab hbc aab aac abc he
  have h₁ : col a b = col a c := congrArg Prod.fst he.1
  have h₂ : col a b = col b c := congrArg Prod.fst he.2
  have ht : MonoTri G col a b c := ⟨hab,hab.trans hbc,aab,aac,abc,h₁,by
    simpa only [min_eq_left hbc.le,max_eq_right hbc.le] using h₂⟩
  have hf : decide (HasLower a b) = decide (HasLower a c) := congrArg Prod.snd he.1
  rcases lt_or_gt_of_ne (hsep a b c ht) with h | h
  · have hlc : HasLower a c := ⟨b,ht,h⟩
    have hlb : HasLower a b := of_decide_eq_true (hf.trans (decide_eq_true hlc))
    obtain ⟨d,hd,hdb⟩ := hlb
    exact hno a d b c hd ht hdb h
  · have hlb : HasLower a b := ⟨c,ht.symm,h⟩
    have hlc : HasLower a c := of_decide_eq_true (hf.symm.trans (decide_eq_true hlb))
    obtain ⟨d,hd,hdc⟩ := hlc
    exact hno a d c b hd ht.symm hdc h

#print axioms countable_cover
end Erdos595LocalInterval
