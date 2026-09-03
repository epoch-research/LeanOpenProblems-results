import Submission.EvenCycleBicliqueCover
import Submission.FiveTupleIterationObstruction

/-!
The first right adjoint of the first five-coordinate candidate is covered.
This is an obstruction to a candidate, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
open Erdos595ArcAdjoint Erdos595BoundedPath Erdos595EvenCycle Erdos595Work
open Erdos595FiveIteration
namespace Erdos595FiveFirst

variable {A : Type*} [LinearOrder A]

private theorem label_ne {x y : Fin 5 → A} (h : H1.Adj x y) : x 0 ≠ y 0 := by
  intro he
  rcases h with (h | h) | (h | h) <;>
    simp only [P10, P11] at h <;>
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ <;> order

private theorem forward_bounds {x y : Fin 5 → A}
    (h : H1.Adj x y) (hxy : x 0 < y 0) :
    x 1 < y 0 ∧ x 2 < y 1 ∧ x 3 < y 2 ∧ x 4 < y 3 ∧ y 0 < x 4 := by
  rcases h with (h | h) | (h | h) <;>
    simp only [P10, P11] at h <;>
    rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ <;>
    (repeat' constructor) <;> order

private theorem no_closing_five (x y : Fin 5 → A)
    (h : Chain (fun a b => H1.Adj a b ∧ a 0 < b 0) 5 x y) : ¬H1.Adj x y := by
  obtain ⟨v4,h4,h4y⟩ := h.split_last
  obtain ⟨v3,h3,h34⟩ := h4.split_last
  obtain ⟨v2,h2,h23⟩ := h3.split_last
  obtain ⟨v1,h1,h12⟩ := h2.split_last
  obtain ⟨v0,h0,h01⟩ := h1.split_last
  cases h0
  have hb01 := forward_bounds h01.1 h01.2
  have hb12 := forward_bounds h12.1 h12.2
  have hb23 := forward_bounds h23.1 h23.2
  have hb34 := forward_bounds h34.1 h34.2
  have hxy : x 0 < y 0 := h01.2.trans (h12.2.trans (h23.2.trans (h34.2.trans h4y.2)))
  intro hclose
  have hc := (forward_bounds hclose hxy).2.2.2.2
  exact (lt_irrefl (x 4))
    (hb01.2.2.2.1.trans (hb12.2.2.1.trans (hb23.2.1.trans
      (hb34.1.trans (h4y.2.trans hc)))))

/-- H1 is ruled out even at its first right-adjoint stage. -/
theorem first_right_cover : IsCountableUnionOfTriangleFree (right (H1 (A := A))) := by
  apply right_cover_of_label H1 (fun x => x 0) 1
  · exact fun _ _ h => label_ne h
  · exact no_closing_five

#print axioms first_right_cover
end Erdos595FiveFirst
