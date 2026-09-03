import Submission.ArcAdjoint
import Submission.LocalIntervalCoverCriterion

/-!
Four minimal three-type disjoint five-coordinate families. A local interval
orientation rules out their first right-adjoint candidates for Erdős 595.
This is auxiliary work, not a settlement of the original conjecture.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open SimpleGraph Set
open Erdos595ArcAdjoint Erdos595Work
namespace Erdos595ThreeFive
variable {A : Type*} [LinearOrder A]
abbrev Point := Fin 5 → A

def P (f : Fin 4) (k : Fin 3) (x y : Point (A := A)) : Prop :=
  ![![x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < x 3 ∧ x 3 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 4 ∧ x 4 < y 3 ∧ y 3 < y 4,
      x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 3 ∧ x 3 < y 3 ∧ y 3 < y 4 ∧ y 4 < x 4,
      x 0 < y 0 ∧ y 0 < x 1 ∧ x 1 < y 1 ∧ y 1 < x 2 ∧ x 2 < x 3 ∧ x 3 < y 2 ∧ y 2 < x 4 ∧ x 4 < y 3 ∧ y 3 < y 4],
    ![x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < x 3 ∧ x 3 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 4 ∧ x 4 < y 3 ∧ y 3 < y 4,
      x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 3 ∧ x 3 < y 3 ∧ y 3 < x 4 ∧ x 4 < y 4,
      x 0 < y 0 ∧ y 0 < y 1 ∧ y 1 < x 1 ∧ x 1 < y 2 ∧ y 2 < y 3 ∧ y 3 < x 2 ∧ x 2 < y 4 ∧ y 4 < x 3 ∧ x 3 < x 4],
    ![x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < x 3 ∧ x 3 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 4 ∧ x 4 < y 3 ∧ y 3 < y 4,
      x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 3 ∧ x 3 < y 3 ∧ y 3 < y 4 ∧ y 4 < x 4,
      x 0 < y 0 ∧ y 0 < y 1 ∧ y 1 < x 1 ∧ x 1 < y 2 ∧ y 2 < y 3 ∧ y 3 < x 2 ∧ x 2 < y 4 ∧ y 4 < x 3 ∧ x 3 < x 4],
    ![x 0 < x 1 ∧ x 1 < x 2 ∧ x 2 < y 0 ∧ y 0 < x 3 ∧ x 3 < y 1 ∧ y 1 < x 4 ∧ x 4 < y 2 ∧ y 2 < y 3 ∧ y 3 < y 4,
      x 0 < x 1 ∧ x 1 < y 0 ∧ y 0 < x 2 ∧ x 2 < y 1 ∧ y 1 < x 3 ∧ x 3 < y 2 ∧ y 2 < y 3 ∧ y 3 < y 4 ∧ y 4 < x 4,
      x 0 < y 0 ∧ y 0 < y 1 ∧ y 1 < y 2 ∧ y 2 < x 1 ∧ x 1 < y 3 ∧ y 3 < x 2 ∧ x 2 < y 4 ∧ y 4 < x 3 ∧ x 3 < x 4]] f k

private theorem first_lt (f : Fin 4) (k : Fin 3) (x y : Point (A := A))
    (h : P f k x y) : x 0 < y 0 := by
  fin_cases f <;> fin_cases k
  · exact (h.1).trans (h.2.1)
  · exact (h.1).trans (h.2.1)
  · exact h.1
  · exact (h.1).trans (h.2.1)
  · exact (h.1).trans (h.2.1)
  · exact h.1
  · exact (h.1).trans (h.2.1)
  · exact (h.1).trans (h.2.1)
  · exact h.1
  · exact (h.1).trans ((h.2.1).trans (h.2.2.1))
  · exact (h.1).trans (h.2.1)
  · exact h.1

def G (f : Fin 4) : SimpleGraph (Point (A := A)) where
  Adj x y := (P f 0 x y ∨ P f 1 x y ∨ P f 2 x y) ∨
    (P f 0 y x ∨ P f 1 y x ∨ P f 2 y x)
  symm := fun _ _ h => h.symm
  loopless := by
    intro x h
    rcases h with (h | h | h) | (h | h | h) <;>
      exact (lt_irrefl _) (first_lt _ _ _ _ h)

private theorem label_ne (f : Fin 4) {x y : Point (A := A)} (h : (G f).Adj x y) :
    x 0 ≠ y 0 := by
  rcases h with (h | h | h) | (h | h | h)
  all_goals first | exact (first_lt _ _ _ _ h).ne | exact (first_lt _ _ _ _ h).ne.symm

private theorem forward (f : Fin 4) {x y : Point (A := A)}
    (h : (G f).Adj x y) (hxy : x 0 < y 0) : P f 0 x y ∨ P f 1 x y ∨ P f 2 x y := by
  rcases h with h | (h | h | h)
  · exact h
  all_goals exact (lt_asymm hxy (first_lt _ _ _ _ h)).elim

private def longType (f : Fin 4) : Fin 3 := if f = 0 then 0 else 1
private def lastType (f : Fin 4) : Fin 3 := if f = 0 then 1 else 0

def T (f : Fin 4) (x y z : Point (A := A)) : Prop :=
  P f 2 x y ∧ P f (longType f) x z ∧ P f (lastType f) y z

private theorem triangle_ordered (f : Fin 4) (x y z : Point (A := A))
    (hxy : x 0 < y 0) (hyz : y 0 < z 0)
    (h₁ : (G f).Adj x y) (h₂ : (G f).Adj x z) (h₃ : (G f).Adj y z) : T f x y z := by
  have f₁ := forward f h₁ hxy
  have f₂ := forward f h₂ (hxy.trans hyz)
  have f₃ := forward f h₃ hyz
  fin_cases f
  · rcases f₁ with f₁ | f₁ | f₁ <;> rcases f₂ with f₂ | f₂ | f₂ <;> rcases f₃ with f₃ | f₃ | f₃
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans (f₂.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans (f₂.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans (f₂.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₃.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans (f₂.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans (f₂.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans (f₂.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.1).trans ((f₂.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.1)))))
    · exact ⟨f₁,f₂,f₃⟩
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₃.2.2.2.1).trans ((f₃.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₂.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₃.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₃.2.2.2.2.1).trans ((f₃.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₃.2.1).trans (f₂.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₃.2.1).trans (f₂.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.1))))
  · rcases f₁ with f₁ | f₁ | f₁ <;> rcases f₂ with f₂ | f₂ | f₂ <;> rcases f₃ with f₃ | f₃ | f₃
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.2.2.1).trans (f₂.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₂.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₁.2.2.2.2.2.1).trans ((f₃.2.2.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₂.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₃.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₂.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.2).trans ((f₃.2.2.2.2.2.2.2.2).trans ((f₂.2.2.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₂.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans ((f₂.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₁.2.2.2.2.2.2.2.2).trans ((f₂.2.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₂.2.1).trans ((f₃.2.1).trans (f₃.2.2.1)))))
    · exact ⟨f₁,f₂,f₃⟩
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₂.2.1).trans ((f₃.2.1).trans (f₃.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.2.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.2.2.1))))
  · rcases f₁ with f₁ | f₁ | f₁ <;> rcases f₂ with f₂ | f₂ | f₂ <;> rcases f₃ with f₃ | f₃ | f₃
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.2.2.1).trans (f₂.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₂.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₁.2.2.2.2.2.1).trans ((f₃.2.2.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₂.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₃.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₂.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₂.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans ((f₂.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.1).trans ((f₂.2.2.2.2.1).trans ((f₂.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₂.2.1).trans ((f₃.2.1).trans (f₃.2.2.1)))))
    · exact ⟨f₁,f₂,f₃⟩
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₃.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₂.2.1).trans ((f₃.2.1).trans (f₃.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.2.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.1).trans (f₃.2.2.2.2.2.2.2.1))))
  · rcases f₁ with f₁ | f₁ | f₁ <;> rcases f₂ with f₂ | f₂ | f₂ <;> rcases f₃ with f₃ | f₃ | f₃
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans ((f₃.2.2.1).trans (f₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.1).trans (f₃.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₃.2.2.1).trans (f₂.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₃.1).trans ((f₃.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₃.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₁.2.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₁.2.2.2.2.2.2.2.1).trans ((f₁.2.2.2.2.2.2.2.2).trans ((f₃.2.2.2.2.2.2.1).trans (f₂.2.2.2.1)))))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₁.2.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₂.2.1).trans ((f₂.2.2.1).trans (f₂.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.2.1).trans (f₂.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₃.2.2.1).trans (f₂.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.2.2.2).trans ((f₂.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.2.1).trans ((f₂.2.2.2.2.2.2.2.2).trans (f₃.2.2.2.2.2.2.2.2))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₂.2.2.2.2.1).trans ((f₃.2.2.1).trans (f₃.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans ((f₃.2.2.1).trans (f₂.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.1).trans (f₂.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₂.2.2.2.2.2.1).trans (f₃.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₁.2.2.2.2.2.2.1).trans ((f₁.2.2.2.2.2.2.2.1).trans ((f₃.2.2.2.2.2.2.1).trans (f₂.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.1).trans ((f₃.1).trans ((f₃.2.1).trans ((f₂.2.1).trans ((f₂.2.2.1).trans (f₂.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₃.2.2.2.2.1).trans (f₂.2.2.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.2.1).trans ((f₂.2.2.1).trans (f₃.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₂.2.1).trans ((f₂.2.2.1).trans (f₃.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₁.2.2.2.1).trans ((f₂.2.1).trans ((f₂.2.2.1).trans ((f₃.2.1).trans ((f₃.2.2.1).trans (f₃.2.2.2.1))))))))
    · exact ⟨f₁,f₂,f₃⟩
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₂.2.1).trans (f₃.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.1).trans ((f₁.2.2.2.1).trans ((f₂.2.1).trans ((f₃.2.1).trans ((f₃.2.2.1).trans (f₃.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.2.2.2.1).trans ((f₂.2.2.1).trans (f₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.2.1).trans ((f₃.2.2.2.2.2.1).trans (f₂.2.2.2.1))))
    · exact False.elim ((lt_irrefl _) ((f₁.2.2.2.1).trans ((f₂.2.2.2.2.1).trans (f₃.2.2.2.2.2.1))))

private theorem triangle_cases (f : Fin 4) (x y z : Point (A := A))
    (h₁ : (G f).Adj x y) (h₂ : (G f).Adj x z) (h₃ : (G f).Adj y z) :
    T f x y z ∨ T f x z y ∨ T f y x z ∨ T f y z x ∨ T f z x y ∨ T f z y x := by
  rcases lt_or_gt_of_ne (label_ne f h₁) with hxy | hyx
  · rcases lt_or_gt_of_ne (label_ne f h₃) with hyz | hzy
    · exact Or.inl (triangle_ordered f x y z hxy hyz h₁ h₂ h₃)
    · rcases lt_or_gt_of_ne (label_ne f h₂) with hxz | hzx
      · exact Or.inr (Or.inl (triangle_ordered f x z y hxz hzy h₂ h₁ h₃.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (triangle_ordered f z x y hzx hxy h₂.symm h₃.symm h₁)))))
  · rcases lt_or_gt_of_ne (label_ne f h₂) with hxz | hzx
    · exact Or.inr (Or.inr (Or.inl (triangle_ordered f y x z hyx hxz h₁.symm h₃ h₂)))
    · rcases lt_or_gt_of_ne (label_ne f h₃) with hyz | hzy
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (triangle_ordered f y z x hyz hzx h₃ h₁.symm h₂.symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (triangle_ordered f z y x hzy hyx h₃.symm h₂.symm h₁.symm)))))

def U (f : Fin 4) (ab ba ac ca bc cb : Point (A := A)) : Prop :=
  (T f ab bc ca ∧ (if f = 0 then T f ac ba cb else T f cb ac ba)) ∨
  (T f bc ab ca ∧ (if f = 0 then T f ac cb ba else T f ba ac cb))

/-- Only matching type zero can occur in a homogeneous right triangle. -/
private theorem uniform_triangle (f : Fin 4) (k : Fin 3)
    (ab ba ac ca bc cb : Point (A := A))
    (hab : P f k ab ba) (hac : P f k ac ca) (hbc : P f k bc cb)
    (h₁ : (G f).Adj ab bc) (h₂ : (G f).Adj ab ca) (h₃ : (G f).Adj bc ca)
    (h₄ : (G f).Adj ac cb) (h₅ : (G f).Adj ac ba) (h₆ : (G f).Adj cb ba) :
    k = 0 ∧ U f ab ba ac ca bc cb := by
  have t₁ := triangle_cases f ab bc ca h₁ h₂ h₃
  have t₂ := triangle_cases f ac cb ba h₄ h₅ h₆
  fin_cases f <;> fin_cases k
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.1)))))))
    · exact ⟨rfl,Or.inl ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((hac.2.1).trans (t₁.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.1).trans ((t₂.2.1.1).trans (t₂.2.1.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans (t₁.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact ⟨rfl,Or.inr ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.1.2.1).trans ((hbc.2.1).trans (t₂.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((hac.2.1).trans ((t₁.1.2.1).trans ((hbc.2.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.2.2.2.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((hac.2.1).trans (t₁.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans ((t₁.1.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.2.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans ((t₁.1.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.1).trans ((hac.2.1).trans (t₁.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.2.1).trans (t₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.1).trans (t₁.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.2.1).trans (t₂.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((t₁.2.2.2.1).trans ((hbc.1).trans (t₂.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans ((t₂.2.1.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.1.2.1).trans ((hac.1).trans (t₁.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.2.2.1).trans ((hac.2.1).trans (t₂.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.2.2.1).trans ((hac.2.1).trans (t₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.2.1).trans ((hac.2.2.1).trans (t₁.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.2.1).trans ((hbc.2.2.1).trans (t₂.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((t₁.1.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hbc.2.1).trans (t₁.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.2.2.1).trans ((hbc.1).trans ((t₂.2.1.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₁.2.2.2.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans (t₁.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.2.1).trans ((hac.2.2.1).trans (t₁.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((t₁.2.1.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hbc.2.1).trans (t₁.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1))))))
    · exact ⟨rfl,Or.inl ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact ⟨rfl,Or.inr ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans ((t₂.1.2.1).trans (t₂.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.2).trans ((t₁.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.2).trans (t₁.2.1.2.2.2.2.2.2.2.2))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₂.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.1.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₂.2.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.2).trans (t₁.2.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₂.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₂.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₂.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.2).trans (t₁.2.1.2.2.2.2.2.2.2.2))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.2))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((hac.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.2).trans (t₂.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans ((hbc.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.1).trans ((hac.2.1).trans ((hac.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.1.2.2.1).trans ((hac.2.2.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.1.2.2.1).trans ((hac.2.2.1).trans (t₂.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans (t₁.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.1).trans ((hac.1).trans (t₁.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1))))))
    · exact ⟨rfl,Or.inl ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((hab.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact ⟨rfl,Or.inr ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((hac.2.1).trans ((t₁.1.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.1).trans ((t₂.2.1.1).trans (t₂.2.1.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans ((t₂.1.2.1).trans (t₂.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.1.1)))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.2.1.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.2.2.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.1).trans ((t₁.1.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.2.2.1).trans ((hbc.1).trans ((hbc.2.1).trans (t₂.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.1.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.2).trans (t₂.2.1.2.2.2.2.2.2.2.2))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.2).trans (t₂.2.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans ((hbc.2.1).trans (t₂.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.1.2.2.1).trans ((hac.2.2.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₁.1.2.2.1).trans ((hac.2.2.1).trans (t₂.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans (t₁.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.1).trans ((hac.1).trans (t₁.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((t₂.2.1.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₁.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.1).trans (t₁.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))))
    · exact ⟨rfl,Or.inl ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans (t₂.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.2))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.2.1.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.1.1).trans ((t₂.1.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.1).trans ((t₁.1.2.1).trans ((t₁.1.2.2.1).trans (t₁.1.2.2.2.1)))))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans (t₂.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₂.1.1)))))
    · exact ⟨rfl,Or.inr ⟨t₁,t₂⟩⟩
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((t₂.1.2.2.1).trans (t₂.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₁.2.1.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.1).trans ((t₁.1.2.1).trans ((t₁.1.2.2.1).trans (t₁.2.2.2.2.1)))))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.1.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans ((t₂.2.1.1).trans (t₂.2.1.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans (t₂.1.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.1).trans ((t₁.2.1.1).trans (t₁.2.1.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.1.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.2.1.1).trans ((t₂.2.1.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((t₂.1.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.1))))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hac.2.1).trans (t₁.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.1.2.2.2.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans (t₁.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.1.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.1.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((t₂.1.2.2.1).trans (t₂.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.2.2.1).trans ((hbc.2.2.2.1).trans ((t₂.1.2.2.1).trans (t₂.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.2.1).trans ((hac.2.2.1).trans (t₂.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.2.2)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((hac.2.1).trans (t₁.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans (t₁.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.2.2.1).trans ((t₁.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.1.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.1.2.2.1).trans ((t₂.1.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₁.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.1.1).trans ((hbc.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.1).trans ((hbc.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans (t₂.2.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₂.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.2).trans ((t₂.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.2.1.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.1).trans ((hbc.2.1).trans (t₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₁.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.2).trans (t₁.2.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.1.2.1).trans ((t₂.1.2.2.1).trans ((t₂.2.2.2.2.1).trans ((hbc.2.2.1).trans (t₁.2.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((t₁.2.1.1).trans ((t₁.1.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((t₂.2.1.1).trans ((t₂.1.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.1.2.2.2.2.2.2.2.2).trans ((hac.2.2.2.2.2.2.2.2).trans (t₂.2.1.2.2.2.2.2.2.2.2)))))
  · rcases t₁ with t₁ | t₁ | t₁ | t₁ | t₁ | t₁ <;>
      rcases t₂ with t₂ | t₂ | t₂ | t₂ | t₂ | t₂
    · exact False.elim ((lt_irrefl _) ((hac.2.1).trans ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₂.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.2).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans ((t₁.1.2.2.1).trans (t₁.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₂.2.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.1.2.2.2.2.1).trans ((hac.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.1).trans ((hab.2.2.1).trans ((hab.2.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.1.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.2.1.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.1).trans ((hac.2.1).trans ((hac.2.2.1).trans ((hac.2.2.2.1).trans (t₂.1.2.2.2.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.1.2.2.1).trans ((t₁.1.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.2.2.2)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.1.2.2.2.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.1.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hbc.2.1).trans ((hbc.2.2.1).trans ((hbc.2.2.2.1).trans (t₁.2.1.2.1)))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.1).trans ((t₁.2.2.2.2.1).trans ((hbc.1).trans (t₂.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((hac.2.1).trans ((t₁.2.1.2.1).trans ((hbc.1).trans (t₂.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.1).trans ((hac.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans (t₁.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((hab.2.1).trans ((t₂.2.1.2.1).trans ((hac.1).trans (t₁.1.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.1).trans (t₁.2.2.2.2.1)))))
    · exact False.elim ((lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((hbc.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1))))))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.1).trans ((hbc.1).trans (t₂.1.1)))))
    · exact False.elim ((lt_irrefl _) ((hac.1).trans ((t₁.1.1).trans ((hbc.1).trans ((hbc.2.1).trans (t₂.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hab.1).trans ((t₂.1.1).trans ((hac.1).trans ((hac.2.1).trans (t₁.2.1.2.1))))))
    · exact False.elim ((lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.1).trans ((hbc.2.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))

private theorem uniform_intervals (f : Fin 4)
    (ab ba ac ca bc cb : Point (A := A)) (h : U f ab ba ac ca bc cb) :
    ba 1 < ac 3 ∨ ca 1 < ab 3 := by
  fin_cases f
  · rcases h with h | h
    · exact Or.inl ((h.2.1.2.2.2.1).trans (h.2.1.2.2.2.2.1))
    · exact Or.inr ((h.1.2.1.2.2.2.2.2.1).trans (h.1.2.2.2.2.2.2.2.1))
  · rcases h with h | h
    · exact Or.inr ((h.1.2.1.2.2.2.2.1).trans (h.1.2.1.2.2.2.2.2.1))
    · exact Or.inl ((h.2.1.2.2.2.1).trans (h.2.1.2.2.2.2.1))
  · rcases h with h | h
    · exact Or.inr ((h.1.2.1.2.2.2.2.1).trans (h.1.2.1.2.2.2.2.2.1))
    · exact Or.inl ((h.2.1.2.2.2.1).trans (h.2.1.2.2.2.2.1))
  · rcases h with h | h
    · exact Or.inr (h.1.2.1.2.2.2.2.1)
    · exact Or.inl (h.2.1.2.2.2.2.1)

private theorem zero_interval (f : Fin 4) (x y : Point (A := A))
    (h : P f 0 x y) : x 3 < y 1 := by
  fin_cases f <;> exact h.2.2.2.2.1

/-- A two-edge path cannot increase through the three associated intervals. -/
private theorem interval_no_path (f : Fin 4)
    (ab ba ac ca ad da bc cb cd dc : Point (A := A))
    (hab : P f 0 ab ba) (hac : P f 0 ac ca) (had : P f 0 ad da)
    (ht₁ : (P f 0 bc cb ∧ U f ab ba ac ca bc cb) ∨
      (P f 0 cb bc ∧ U f ac ca ab ba cb bc))
    (ht₂ : (P f 0 cd dc ∧ U f ac ca ad da cd dc) ∨
      (P f 0 dc cd ∧ U f ad da ac ca dc cd))
    (hfwd : (G f).Adj bc cd) (hrev : (G f).Adj dc cb)
    (hleft : (G f).Adj ba ad) (hright : (G f).Adj ab da)
    (hlo₁ : ba 1 < ac 3) (hlo₂ : ca 1 < ad 3) : False := by
  fin_cases f
  · rcases ht₁ with ⟨h₁,t₁⟩ | ⟨h₁,t₁⟩ <;> rcases ht₂ with ⟨h₂,t₂⟩ | ⟨h₂,t₂⟩ <;>
      rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.1).trans (t₁.1.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.2.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₁.2.2.1.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((e4.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.2.2.1).trans (t₂.1.1.2.2.2.2.2.2.2.1))))
    · exact (lt_irrefl _) ((t₂.2.2.1.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₁.2.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₂.1.2.1.2.2.2.2.1).trans (hlo₂))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · rcases hleft with (e3 | e3 | e3) | (e3 | e3 | e3)
        · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((e3.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((t₁.1.2.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1)))))
        · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans (t₂.1.2.2.2.1)))))
        · exact (lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((e3.2.2.1).trans ((t₂.1.2.2.2.1).trans (t₁.1.2.1.2.2.1)))))
        · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((hlo₂).trans ((e3.2.2.2.2.1).trans (hlo₁))))
        · exact (lt_irrefl _) ((h₂.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans ((t₁.2.2.2.2.1).trans (e4.2.2.1)))))
        · exact (lt_irrefl _) ((h₁.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e3.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.1).trans ((h₁.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans ((h₂.2.2.2.2.1).trans (t₂.2.1.2.2.2.1))))))
      · exact (lt_irrefl _) ((h₂.2.1).trans ((t₂.2.1.2.1).trans ((t₁.2.2.1.2.1).trans (e4.2.1))))
      · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.2.1.2.1).trans ((t₁.1.2.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans (t₂.1.2.1.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.1).trans ((e4.2.2.1).trans (t₂.1.2.1.2.1)))))
    · exact (lt_irrefl _) ((t₁.2.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.1.2.2.2.2.1).trans (hlo₁))
    · rcases hfwd with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((h₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.1.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.1).trans ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.1.1.2.1).trans (t₁.1.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.2).trans ((t₁.2.2.2.2.2.2.2.2.2.2.2).trans ((e4.2.2.2.2.2.2.2.1).trans ((h₂.2.2.2.2.1).trans ((h₂.2.2.2.2.2.1).trans (t₂.2.2.2.2.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.2.2).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₁.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
    · exact (lt_irrefl _) ((t₂.2.2.1.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₁.1.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.1.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₂.1.2.1.2.2.2.2.1).trans (hlo₂))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.1).trans ((t₂.1.2.1.2.2.1).trans ((h₂.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₁.1.1.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.1).trans ((t₂.1.2.1.2.2.1).trans ((e4.2.2.2.1).trans (t₁.1.1.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((h₂.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((t₁.2.2.2.2.1).trans ((t₂.1.2.1.2.2.1).trans (e4.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1))))
  · rcases ht₁ with ⟨h₁,t₁⟩ | ⟨h₁,t₁⟩ <;> rcases ht₂ with ⟨h₂,t₂⟩ | ⟨h₂,t₂⟩ <;>
      rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₂.2.2.2.2.2.2.2.1).trans (hlo₂))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.1).trans (t₁.1.2.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.1).trans (t₁.1.2.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₁.2.2.1).trans ((t₁.1.2.1.2.2.2.1).trans ((t₂.2.2.1.2.1).trans (e4.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.2.2.1.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.2.2.1.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1))))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · rcases hleft with (e3 | e3 | e3) | (e3 | e3 | e3)
        · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((e3.2.2.2.2.1).trans ((t₂.1.2.1.2.1).trans ((t₁.1.2.1.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1)))))
        · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans (t₂.1.2.1.2.1)))))
        · exact (lt_irrefl _) ((h₁.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e3.2.2.2.2.2.1).trans (t₁.2.2.1.2.2.2.1)))))
        · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((hlo₂).trans ((e3.2.2.2.2.1).trans (hlo₁))))
        · exact (lt_irrefl _) ((h₂.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans ((t₁.2.2.1.2.1).trans (e4.2.2.1)))))
        · exact (lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((e3.2.2.1).trans ((t₂.1.2.1.2.1).trans (t₁.1.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.1).trans (t₂.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((t₁.1.2.1.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.1).trans ((t₁.2.2.2.2.1).trans ((e4.1).trans ((h₂.1).trans ((h₂.2.1).trans (t₂.2.1.1))))))
    · exact (lt_irrefl _) ((t₂.1.2.2.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₂.2.2.2.2.2.2.2.1).trans (hlo₂))
    · rcases hfwd with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((h₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.1.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.1).trans ((t₁.1.1.2.2.2.1).trans ((h₁.2.2.2.1).trans ((h₁.2.2.2.2.1).trans ((e4.2.1).trans (t₂.1.1.1))))))
      · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.1.2.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.1.2.1.2.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((h₁.2.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.2.2.1.2.1)))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((h₂.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1)))))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.1).trans ((t₂.1.2.2.2.2.1).trans ((h₂.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₁.1.1.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.1).trans ((t₂.1.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.1.1.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((t₁.2.2.1.2.1).trans ((t₂.1.2.2.2.2.1).trans (e4.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((h₂.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.1)))))
    · exact (lt_irrefl _) ((t₂.1.2.2.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
  · rcases ht₁ with ⟨h₁,t₁⟩ | ⟨h₁,t₁⟩ <;> rcases ht₂ with ⟨h₂,t₂⟩ | ⟨h₂,t₂⟩ <;>
      rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₂.2.2.2.2.2.2.2.1).trans (hlo₂))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.1).trans (t₁.1.2.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.1).trans (t₁.1.2.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₁.2.2.1).trans ((t₁.1.2.1.2.2.2.1).trans ((t₂.2.2.1.2.1).trans (e4.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.2.2.1.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.1).trans ((t₂.2.2.1.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.2.2.2.1))))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · rcases hleft with (e3 | e3 | e3) | (e3 | e3 | e3)
        · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((e3.2.2.2.2.1).trans ((t₂.1.2.1.2.1).trans ((t₁.1.2.1.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1)))))
        · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans (t₂.1.2.1.2.1)))))
        · exact (lt_irrefl _) ((h₁.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e3.2.2.2.2.2.1).trans (t₁.2.2.1.2.2.2.1)))))
        · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((hlo₂).trans ((e3.2.2.2.2.1).trans (hlo₁))))
        · exact (lt_irrefl _) ((h₂.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans ((t₁.2.2.1.2.1).trans (e4.2.2.1)))))
        · exact (lt_irrefl _) ((hab.2.2.2.1).trans ((hab.2.2.2.2.1).trans ((e3.2.2.1).trans ((t₂.1.2.1.2.1).trans (t₁.1.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((h₁.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans ((h₂.2.2.2.2.1).trans (t₂.2.1.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.1).trans (t₂.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hab.2.2.2.2.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.2.2.2.1).trans ((t₁.1.2.1.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.1).trans ((t₁.2.2.2.2.1).trans ((e4.1).trans ((h₂.1).trans ((h₂.2.1).trans (t₂.2.1.1))))))
    · exact (lt_irrefl _) ((t₂.1.2.2.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₂.2.2.2.2.2.2.2.1).trans (hlo₂))
    · rcases hfwd with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((h₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.1.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.1).trans ((t₁.1.1.2.2.2.1).trans ((h₁.2.2.2.1).trans ((h₁.2.2.2.2.1).trans ((e4.2.1).trans (t₂.1.1.1))))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.1).trans ((hac.2.2.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₁.2.2.1.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.2.2).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₁.2.2.1.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.1).trans ((hac.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.2.2.1.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.2).trans ((t₁.2.2.1.2.2.2.2.2.2.2.2).trans ((e4.2.2.2.2.2.2.2.1).trans ((h₂.2.2.2.2.1).trans ((h₂.2.2.2.2.2.1).trans (t₂.2.2.1.2.2.2.2.2.1))))))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.1).trans ((t₂.1.2.2.2.2.1).trans ((h₂.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₁.1.1.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.1).trans ((t₂.1.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.1.1.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.1).trans ((t₂.2.1.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.1).trans (e4.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((t₁.2.2.1.2.1).trans ((t₂.1.2.2.2.2.1).trans (e4.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.2.1.2.2.2.2.2.1).trans ((h₂.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.2.1).trans (t₁.1.1.2.2.2.2.2.1)))))
    · exact (lt_irrefl _) ((t₂.1.2.2.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
  · rcases ht₁ with ⟨h₁,t₁⟩ | ⟨h₁,t₁⟩ <;> rcases ht₂ with ⟨h₂,t₂⟩ | ⟨h₂,t₂⟩ <;>
      rcases t₁ with t₁ | t₁ <;> rcases t₂ with t₂ | t₂
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₂.2.2.2.2.2.2.2.1).trans (hlo₂))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.2.2.1).trans ((e4.2.2.1).trans ((h₁.2.2.2.1).trans (t₁.1.2.1.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₁.2.2.2.1).trans ((t₁.1.2.1.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.1).trans (e4.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₂.2.2.1.2.1).trans ((e4.1).trans (t₁.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((had.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.2.2.1).trans ((e4.2.2.1).trans (t₂.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.2).trans ((t₁.1.2.1.2.2.2.2.2.2.2.2).trans ((h₁.2.2.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₂.2.2.1.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans ((t₂.2.2.1.2.2.2.2.2.2.2.2).trans (t₁.1.2.1.2.2.2.2.2.2.2.2))))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.2.2.2.2.2.2.2.1).trans (hlo₁))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · rcases hleft with (e3 | e3 | e3) | (e3 | e3 | e3)
        · exact (lt_irrefl _) ((t₁.2.2.1.2.2.2.2.1).trans ((e3.2.2.2.2.1).trans ((t₂.1.1.2.2.2.2.1).trans (e4.2.2.2.2.1))))
        · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans (t₂.1.2.1.2.1))))
        · exact (lt_irrefl _) ((t₁.2.2.1.2.1).trans ((e4.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans (e3.2.2.2.1))))
        · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₂.1.2.1.2.2.2.2.1).trans ((e3.2.2.2.2.1).trans (t₁.2.1.2.2.2.2.1))))
        · exact (lt_irrefl _) ((t₁.2.2.1.2.1).trans ((e4.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans (e3.2.2.2.1))))
        · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.1.2.2.2.2.2.1).trans ((e3.2.2.2.1).trans (t₂.1.2.1.2.1))))
      · exact (lt_irrefl _) ((h₁.2.2.1).trans ((e4.2.2.1).trans ((t₂.1.2.2.2.2.1).trans (t₁.1.2.1.2.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.1).trans ((h₁.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((e4.2.1).trans ((h₁.2.2.2.2.2.2.2.1).trans ((h₁.2.2.2.2.2.2.2.2).trans ((e4.2.2.2.2.2.2.1).trans (t₂.1.2.2.2.2.1)))))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((e4.2.1).trans ((h₂.1).trans ((h₂.2.1).trans (t₂.1.2.2.2.2.1))))))
      · exact (lt_irrefl _) ((h₁.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.1).trans (t₁.1.2.1.2.2.2.2.1))))
    · exact (lt_irrefl _) ((t₂.1.2.2.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₂.2.2.2.2.2.2.2.1).trans (hlo₂))
    · rcases hfwd with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₁.2.2.1.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₂.1.1.2.2.2.2.1))))
      · exact (lt_irrefl _) ((hac.1).trans ((t₁.1.1.2.2.2.2.1).trans ((h₁.2.2.2.2.1).trans ((e4.2.1).trans (t₂.1.1.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.2.2.1.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.2.2.2).trans ((t₂.1.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.1).trans (t₁.2.2.1.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.1).trans ((t₂.1.1.2.2.2.2.2.1).trans ((e4.2.2.2.1).trans (t₁.2.2.1.2.1))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.2.2.2.2).trans ((t₁.2.2.1.2.2.2.2.2.2.2.2).trans ((e4.2.2.2.2.2.2.2.1).trans ((h₂.2.2.2.2.1).trans (t₂.2.2.1.2.2.2.2.1)))))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · rcases hrev with (e4 | e4 | e4) | (e4 | e4 | e4)
      · exact (lt_irrefl _) ((hab.2.2.2.1).trans ((t₁.2.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans (t₁.1.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((h₂.2.2.1).trans ((t₂.2.1.1).trans ((t₁.1.1.1).trans (e4.2.2.1))))
      · exact (lt_irrefl _) ((hac.1).trans ((t₁.1.1.2.2.2.2.1).trans ((e4.2.2.2.2.2.1).trans ((h₂.2.2.1).trans (t₂.2.1.1)))))
      · exact (lt_irrefl _) ((hab.2.2.2.2.1).trans ((t₁.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.1).trans ((t₂.1.2.2.2.2.1).trans (t₁.2.2.2.2.2.2.1)))))
      · exact (lt_irrefl _) ((hac.2.2.2.2.1).trans ((t₂.1.2.2.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.2.2).trans (t₁.1.1.2.2.2.2.2.2.2.1))))
      · exact (lt_irrefl _) ((h₂.2.2.2.2.2.1).trans ((e4.2.2.2.2.2.2.2.1).trans ((t₁.1.1.2.2.2.2.2.1).trans (t₂.2.1.2.2.2.1))))
    · exact (lt_irrefl _) ((t₂.1.2.2.2.2.2.2.1).trans (hlo₂))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))
    · exact (lt_irrefl _) ((t₁.1.2.2.2.2.2.2.1).trans (hlo₁))

/-- Information about a homogeneous right triangle with a fixed root. -/
private structure TriangleData (f : Fin 4) (ab ba ac ca bc cb : Point (A := A)) : Prop where
  left_match : P f 0 ab ba
  right_match : P f 0 ac ca
  choices : (P f 0 bc cb ∧ U f ab ba ac ca bc cb) ∨
    (P f 0 cb bc ∧ U f ac ca ab ba cb bc)

private theorem TriangleData.separation {f : Fin 4}
    {ab ba ac ca bc cb : Point (A := A)} (h : TriangleData f ab ba ac ca bc cb) :
    ba 1 < ac 3 ∨ ca 1 < ab 3 := by
  rcases h.choices with ⟨_,ht⟩ | ⟨_,ht⟩
  · exact uniform_intervals f ab ba ac ca bc cb ht
  · exact (uniform_intervals f ac ca ab ba cb bc ht).symm

private theorem TriangleData.ordered {f : Fin 4}
    {ab ba ac ca bc cb : Point (A := A)} (h : TriangleData f ab ba ac ca bc cb)
    (hlo : ab 3 < ac 3) : ba 1 < ac 3 := by
  rcases h.separation with hs | hs
  · exact hs
  · exact (lt_irrefl (ac 3) ((zero_interval f ac ca h.right_match).trans (hs.trans hlo))).elim

private theorem exists_type (f : Fin 4) (x y : Point (A := A)) (h : (G f).Adj x y) :
    ∃ k : Bool × Fin 3, P f k.2 (if k.1 then y else x) (if k.1 then x else y) := by
  rcases h with (h | h | h) | (h | h | h)
  · exact ⟨(false,0),h⟩
  · exact ⟨(false,1),h⟩
  · exact ⟨(false,2),h⟩
  · exact ⟨(true,0),h⟩
  · exact ⟨(true,1),h⟩
  · exact ⟨(true,2),h⟩

private noncomputable def typeCode (f : Fin 4) (x y : Point (A := A))
    (h : (G f).Adj x y) : Bool × Fin 3 := (exists_type f x y h).choose

private theorem typeCode_spec (f : Fin 4) (x y : Point (A := A)) (h : (G f).Adj x y) :
    P f (typeCode f x y h).2
      (if (typeCode f x y h).1 then y else x) (if (typeCode f x y h).1 then x else y) :=
  (exists_type f x y h).choose_spec

section Pullback
variable {V : Type*} (F : SimpleGraph V) (f : Fin 4) (g : arcGraph F →g G (A := A) f)

private def reverse : arcGraph F →g arcGraph F where
  toFun e := ⟨(e.1.2,e.1.1),e.2.symm⟩
  map_rel' := by
    intro e d h
    exact h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)

private def oriented (s : Bool) : arcGraph F →g G (A := A) f :=
  if s then g.comp (reverse F) else g

private noncomputable def color (a b : V) : Bool × Fin 3 := by
  classical
  exact if h : F.Adj a b then typeCode f (g ⟨(a,b),h⟩) (g ⟨(b,a),h.symm⟩)
    (g.map_adj (Or.inl rfl)) else (false,0)

private theorem pair_type {a b : V} (h : F.Adj a b) (k : Bool × Fin 3)
    (he : color F f g a b = k) :
    P f k.2 ((oriented F f g k.1) ⟨(a,b),h⟩) ((oriented F f g k.1) ⟨(b,a),h.symm⟩) := by
  classical
  have ht := typeCode_spec f (g ⟨(a,b),h⟩) (g ⟨(b,a),h.symm⟩)
    (g.map_adj (Or.inl rfl))
  have hk : typeCode f (g ⟨(a,b),h⟩) (g ⟨(b,a),h.symm⟩)
      (g.map_adj (Or.inl rfl)) = k := by simpa only [color, dif_pos h] using he
  rw [hk] at ht
  unfold oriented
  split_ifs with hs
  · simpa only [hs, if_true] using ht
  · simpa only [hs, if_false] using ht

private theorem triangle_data [LinearOrder V] (a b c : V)
    (h : Erdos595LocalInterval.MonoTri F (color F f g) a b c)
    (k : Bool × Fin 3) (hk : color F f g a b = k) :
    TriangleData f
      ((oriented F f g k.1) ⟨(a,b),h.left_adj⟩)
      ((oriented F f g k.1) ⟨(b,a),h.left_adj.symm⟩)
      ((oriented F f g k.1) ⟨(a,c),h.right_adj⟩)
      ((oriented F f g k.1) ⟨(c,a),h.right_adj.symm⟩)
      ((oriented F f g k.1) ⟨(b,c),h.cross_adj⟩)
      ((oriented F f g k.1) ⟨(c,b),h.cross_adj.symm⟩) := by
  let φ := oriented F f g k.1
  have hab := pair_type F f g h.left_adj k hk
  have hac := pair_type F f g h.right_adj k (h.color_left.symm.trans hk)
  rcases lt_or_gt_of_ne h.cross_adj.ne with hbc | hcb
  · have hc : color F f g b c = k := by
      simpa only [min_eq_left hbc.le,max_eq_right hbc.le] using h.color_cross.symm.trans hk
    have hbc' := pair_type F f g h.cross_adj k hc
    have ht := uniform_triangle f k.2
      (φ ⟨(a,b),h.left_adj⟩) (φ ⟨(b,a),h.left_adj.symm⟩)
      (φ ⟨(a,c),h.right_adj⟩) (φ ⟨(c,a),h.right_adj.symm⟩)
      (φ ⟨(b,c),h.cross_adj⟩) (φ ⟨(c,b),h.cross_adj.symm⟩) hab hac hbc'
      (φ.map_adj (Or.inl rfl)) (φ.map_adj (Or.inr rfl)) (φ.map_adj (Or.inl rfl))
      (φ.map_adj (Or.inl rfl)) (φ.map_adj (Or.inr rfl)) (φ.map_adj (Or.inl rfl))
    rw [ht.1] at hab hac hbc'
    exact ⟨hab,hac,Or.inl ⟨hbc',ht.2⟩⟩
  · have hc : color F f g c b = k := by
      simpa only [min_eq_right hcb.le,max_eq_left hcb.le] using h.color_cross.symm.trans hk
    have hcb' := pair_type F f g h.cross_adj.symm k hc
    have ht := uniform_triangle f k.2
      (φ ⟨(a,c),h.right_adj⟩) (φ ⟨(c,a),h.right_adj.symm⟩)
      (φ ⟨(a,b),h.left_adj⟩) (φ ⟨(b,a),h.left_adj.symm⟩)
      (φ ⟨(c,b),h.cross_adj.symm⟩) (φ ⟨(b,c),h.cross_adj⟩) hac hab hcb'
      (φ.map_adj (Or.inl rfl)) (φ.map_adj (Or.inr rfl)) (φ.map_adj (Or.inl rfl))
      (φ.map_adj (Or.inl rfl)) (φ.map_adj (Or.inr rfl)) (φ.map_adj (Or.inl rfl))
    rw [ht.1] at hab hac hcb'
    exact ⟨hab,hac,Or.inr ⟨hcb',ht.2⟩⟩

private noncomputable def label (a b : V) : WithBot A := by
  classical
  exact if h : F.Adj a b then
    (((oriented F f g (color F f g a b).1) ⟨(a,b),h⟩) 3 : A) else ⊥

private theorem label_eq {a b : V} (h : F.Adj a b) (k : Bool × Fin 3)
    (hk : color F f g a b = k) :
    label F f g a b = ((((oriented F f g k.1) ⟨(a,b),h⟩) 3 : A) : WithBot A) := by
  simp only [label,dif_pos h,hk]

include g in
/-- The interval orientation provides a finite triangle-free edge cover for
any arc source of any of the four families. -/
theorem arc_source_cover : IsCountableUnionOfTriangleFree F := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595LocalInterval.countable_cover F (color F f g) (label F f g)
  · intro a b c ht
    let k := color F f g a b
    let φ := oriented F f g k.1
    have hs := triangle_data F f g a b c ht k rfl
    rw [label_eq F f g ht.left_adj k rfl,
      label_eq F f g ht.right_adj k ht.color_left.symm]
    rcases hs.separation with h | h
    · exact (WithBot.coe_lt_coe.mpr ((zero_interval f _ _ hs.left_match).trans h)).ne
    · exact (WithBot.coe_lt_coe.mpr ((zero_interval f _ _ hs.right_match).trans h)).ne.symm
  · intro a b c d ht₁ ht₂ hlo₁ hlo₂
    let k := color F f g a b
    let φ := oriented F f g k.1
    have hk₂ : color F f g a c = k := ht₁.color_left.symm
    have hk₃ : color F f g a d = k := ht₂.color_left.symm.trans hk₂
    have hs₁ := triangle_data F f g a b c ht₁ k rfl
    have hs₂ := triangle_data F f g a c d ht₂ k hk₂
    rw [label_eq F f g ht₁.left_adj k rfl,
      label_eq F f g ht₁.right_adj k hk₂] at hlo₁
    rw [label_eq F f g ht₂.left_adj k hk₂,
      label_eq F f g ht₂.right_adj k hk₃] at hlo₂
    have h₁ := hs₁.ordered (WithBot.coe_lt_coe.mp hlo₁)
    have h₂ := hs₂.ordered (WithBot.coe_lt_coe.mp hlo₂)
    exact interval_no_path f
      (φ ⟨(a,b),ht₁.left_adj⟩) (φ ⟨(b,a),ht₁.left_adj.symm⟩)
      (φ ⟨(a,c),ht₁.right_adj⟩) (φ ⟨(c,a),ht₁.right_adj.symm⟩)
      (φ ⟨(a,d),ht₂.right_adj⟩) (φ ⟨(d,a),ht₂.right_adj.symm⟩)
      (φ ⟨(b,c),ht₁.cross_adj⟩) (φ ⟨(c,b),ht₁.cross_adj.symm⟩)
      (φ ⟨(c,d),ht₂.cross_adj⟩) (φ ⟨(d,c),ht₂.cross_adj.symm⟩)
      hs₁.left_match hs₁.right_match hs₂.right_match hs₁.choices hs₂.choices
      (φ.map_adj (Or.inl rfl)) (φ.map_adj (Or.inl rfl))
      (φ.map_adj (Or.inl rfl)) (φ.map_adj (Or.inr rfl)) h₁ h₂
end Pullback

/-- All four first-right candidates are covered over every linear order. -/
theorem first_right_cover (f : Fin 4) :
    IsCountableUnionOfTriangleFree (right (G (A := A) f)) :=
  arc_source_cover (right (G f)) f (fromRight SimpleGraph.Hom.id)

#print axioms uniform_triangle
#print axioms interval_no_path
#print axioms uniform_intervals
#print axioms first_right_cover
end Erdos595ThreeFive
