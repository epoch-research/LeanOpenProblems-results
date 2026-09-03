import Submission.NoAlternatingBiclique

/-!
The two surviving triangle-bearing quadruple-type families from the finite
exploration have coverable right adjoints. We prove this for the larger graphs
defined just by the required strict inequalities, allowing irrelevant coordinate
equalities. In particular arbitrary infinite staircase boundaries do not rescue
these right-adjoint candidates. This is not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595DisjointQuadruple
open Erdos595ArcAdjoint Erdos595NoAlternating Erdos595Work

variable {A : Type*} [LinearOrder A]

abbrev Quad (A : Type*) [LinearOrder A] := {x : Fin 4 → A // StrictMono x}

def first (x : Quad A) : A := x.1 0

private def fromForward (R : Quad A → Quad A → Prop)
    (hR : ∀ x y, R x y → first x < first y) : SimpleGraph (Quad A) where
  Adj x y := R x y ∨ R y x
  symm := fun _ _ h => h.symm
  loopless := fun x h => h.elim (fun h => (lt_irrefl _ (hR x x h)))
    (fun h => (lt_irrefl _ (hR x x h)))

private lemma forward_of_lt (R : Quad A → Quad A → Prop)
    (hR : ∀ x y, R x y → first x < first y) {x y : Quad A}
    (hlt : first x < first y) (hadj : (fromForward R hR).Adj x y) : R x y :=
  hadj.resolve_right (fun h => lt_asymm hlt (hR y x h))

private lemma first_ne_of_adj (R : Quad A → Quad A → Prop)
    (hR : ∀ x y, R x y → first x < first y) {x y : Quad A}
    (hadj : (fromForward R hR).Adj x y) : first x ≠ first y :=
  hadj.elim (fun h => (hR x y h).ne) (fun h => (hR y x h).ne.symm)

/-- The four interleavings 00010111, 00011011, 00100111, 00101011,
with the inessential distinctness requirements relaxed. -/
def conjunction (x y : Quad A) : Prop :=
  x.1 1 < y.1 0 ∧ y.1 0 < x.1 3 ∧ x.1 3 < y.1 2 ∧ x.1 2 < y.1 1

lemma conjunction_first (x y : Quad A) (h : conjunction x y) : first x < first y :=
  (x.2 (by decide : (0 : Fin 4) < 1)).trans h.1

def conjunctionGraph (A : Type*) [LinearOrder A] : SimpleGraph (Quad A) :=
  fromForward conjunction conjunction_first

theorem conjunction_no_alternating : NoAlternatingLabel (conjunctionGraph A) first := by
  intro a b c d hab hbc hcd hab' hbc' hcd' hda
  have h₁ := forward_of_lt conjunction conjunction_first hab hab'
  have h₂ := forward_of_lt conjunction conjunction_first hbc hbc'
  have h₃ := forward_of_lt conjunction conjunction_first hcd hcd'
  have h₄ := forward_of_lt conjunction conjunction_first (hab.trans (hbc.trans hcd)) hda.symm
  exact lt_irrefl _ (h₁.2.2.1.trans (h₂.2.2.2.trans (h₃.1.trans h₄.2.1)))

/-- The three interleavings 00101011, 00101101, 01001011,
again allowing equalities not ruled out by the displayed inequalities. -/
def disjunction (x y : Quad A) : Prop :=
  x.1 0 < y.1 0 ∧ y.1 0 < x.1 2 ∧ x.1 2 < y.1 1 ∧
    y.1 1 < x.1 3 ∧ x.1 3 < y.1 3 ∧ (x.1 1 < y.1 0 ∨ x.1 3 < y.1 2)

lemma disjunction_first (x y : Quad A) (h : disjunction x y) : first x < first y := h.1

def disjunctionGraph (A : Type*) [LinearOrder A] : SimpleGraph (Quad A) :=
  fromForward disjunction disjunction_first

theorem disjunction_no_alternating : NoAlternatingLabel (disjunctionGraph A) first := by
  intro a b c d hab hbc hcd hab' hbc' hcd' hda
  have h₁ := forward_of_lt disjunction disjunction_first hab hab'
  have h₂ := forward_of_lt disjunction disjunction_first hbc hbc'
  have h₃ := forward_of_lt disjunction disjunction_first hcd hcd'
  have h₄ := forward_of_lt disjunction disjunction_first (hab.trans (hbc.trans hcd)) hda.symm
  rcases h₂.2.2.2.2.2 with h | h
  · exact lt_asymm h (hcd.trans (h₄.2.1.trans h₁.2.2.1))
  · exact lt_asymm h (h₃.2.2.1.trans (h₄.2.2.2.1.trans h₁.2.2.2.2.1))

theorem conjunction_right_cover :
    IsCountableUnionOfTriangleFree (right (conjunctionGraph A)) := by
  apply right_cover_of_label (conjunctionGraph A) first
  · intro x y h
    exact first_ne_of_adj conjunction conjunction_first h
  · exact conjunction_no_alternating

theorem disjunction_right_cover :
    IsCountableUnionOfTriangleFree (right (disjunctionGraph A)) := by
  apply right_cover_of_label (disjunctionGraph A) first
  · intro x y h
    exact first_ne_of_adj disjunction disjunction_first h
  · exact disjunction_no_alternating

/-- This includes every stricter subgraph, such as the original disjoint-type graph. -/
theorem conjunction_right_cover_of_le (H : SimpleGraph (Quad A))
    (hH : H ≤ conjunctionGraph A) : IsCountableUnionOfTriangleFree (right H) := by
  exact right_cover_of_base_hom (conjunctionGraph A)
    { toFun := id, map_rel' := fun h => hH h } conjunction_right_cover

/-- Inessential coordinate equalities can be forbidden again without losing the cover. -/
theorem disjunction_right_cover_of_le (H : SimpleGraph (Quad A))
    (hH : H ≤ disjunctionGraph A) : IsCountableUnionOfTriangleFree (right H) := by
  exact right_cover_of_base_hom (disjunctionGraph A)
    { toFun := id, map_rel' := fun h => hH h } disjunction_right_cover

#print axioms conjunction_right_cover
#print axioms disjunction_right_cover
end Erdos595DisjointQuadruple
