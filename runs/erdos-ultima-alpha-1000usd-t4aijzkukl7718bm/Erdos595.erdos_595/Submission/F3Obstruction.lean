import Submission.PaleyObstruction

/-!
A finite obstruction to assigning nonconstant F₃-vector-space labels to the
three edges of every triangle, with their sum zero. This is auxiliary work,
not a proof or disproof of Erdős 595.
-/

open SimpleGraph
namespace Erdos595F3Obstruction
open Erdos595Paley

local instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (adjacent a b))

variable {E : Type*} [AddCommGroup E] [Module (ZMod 3) E]

def triangleSum (f : Fin 17 → Fin 17 → E) (a b c : Fin 17) : E :=
  f a b + f a c + f b c

/-- A checked linear combination of 53 triangle relations forces two edges
of a triangle to have equal labels. -/
theorem collapse (f : Fin 17 → Fin 17 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      triangleSum f a b c = 0) : f 0 1 = f 0 2 := by
  have hs : f 0 1 - f 0 2 = 0 := by
    calc
      _ = (1 : ZMod 3) • triangleSum f 0 1 2 +
          (2 : ZMod 3) • triangleSum f 0 2 4 +
          (2 : ZMod 3) • triangleSum f 0 2 15 +
          (2 : ZMod 3) • triangleSum f 0 4 8 +
          (2 : ZMod 3) • triangleSum f 0 4 13 +
          (2 : ZMod 3) • triangleSum f 0 8 9 +
          (2 : ZMod 3) • triangleSum f 0 8 16 +
          (1 : ZMod 3) • triangleSum f 0 9 13 +
          (1 : ZMod 3) • triangleSum f 0 15 16 +
          (1 : ZMod 3) • triangleSum f 1 2 3 +
          (1 : ZMod 3) • triangleSum f 1 2 10 +
          (2 : ZMod 3) • triangleSum f 1 3 16 +
          (1 : ZMod 3) • triangleSum f 1 5 9 +
          (2 : ZMod 3) • triangleSum f 1 5 14 +
          (2 : ZMod 3) • triangleSum f 1 9 10 +
          (1 : ZMod 3) • triangleSum f 1 14 16 +
          (2 : ZMod 3) • triangleSum f 2 3 11 +
          (1 : ZMod 3) • triangleSum f 2 4 6 +
          (2 : ZMod 3) • triangleSum f 2 6 15 +
          (2 : ZMod 3) • triangleSum f 2 10 11 +
          (2 : ZMod 3) • triangleSum f 2 11 15 +
          (1 : ZMod 3) • triangleSum f 3 4 5 +
          (2 : ZMod 3) • triangleSum f 3 4 12 +
          (2 : ZMod 3) • triangleSum f 3 5 7 +
          (2 : ZMod 3) • triangleSum f 3 7 11 +
          (2 : ZMod 3) • triangleSum f 3 7 16 +
          (2 : ZMod 3) • triangleSum f 3 11 12 +
          (2 : ZMod 3) • triangleSum f 3 12 16 +
          (2 : ZMod 3) • triangleSum f 4 5 13 +
          (2 : ZMod 3) • triangleSum f 4 6 8 +
          (2 : ZMod 3) • triangleSum f 4 8 12 +
          (2 : ZMod 3) • triangleSum f 4 12 13 +
          (1 : ZMod 3) • triangleSum f 5 6 7 +
          (2 : ZMod 3) • triangleSum f 5 6 14 +
          (2 : ZMod 3) • triangleSum f 5 9 13 +
          (2 : ZMod 3) • triangleSum f 5 13 14 +
          (2 : ZMod 3) • triangleSum f 6 7 15 +
          (1 : ZMod 3) • triangleSum f 6 8 10 +
          (2 : ZMod 3) • triangleSum f 6 10 14 +
          (2 : ZMod 3) • triangleSum f 6 14 15 +
          (1 : ZMod 3) • triangleSum f 7 8 9 +
          (2 : ZMod 3) • triangleSum f 7 8 16 +
          (2 : ZMod 3) • triangleSum f 7 9 11 +
          (2 : ZMod 3) • triangleSum f 7 11 15 +
          (2 : ZMod 3) • triangleSum f 7 15 16 +
          (2 : ZMod 3) • triangleSum f 8 10 12 +
          (2 : ZMod 3) • triangleSum f 8 12 16 +
          (1 : ZMod 3) • triangleSum f 9 10 11 +
          (1 : ZMod 3) • triangleSum f 10 12 14 +
          (1 : ZMod 3) • triangleSum f 11 12 13 +
          (2 : ZMod 3) • triangleSum f 11 13 15 +
          (2 : ZMod 3) • triangleSum f 12 14 16 +
          (1 : ZMod 3) • triangleSum f 13 14 15 := by
        unfold triangleSum
        match_scalars <;> decide
      _ = 0 := by
        rw [h 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 2 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 4 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 8 9 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 8 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 9 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 15 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 2 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 3 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 5 9 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 5 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 14 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 3 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 6 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 10 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 11 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 4 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 7 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 7 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 11 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 12 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 4 5 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 4 6 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 4 8 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 4 12 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 5 6 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 5 9 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 5 13 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 6 7 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 6 8 10 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 6 10 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 6 14 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 7 8 9 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 7 8 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 7 9 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 7 11 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 7 15 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 8 10 12 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 8 12 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 9 10 11 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 10 12 14 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 11 12 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 11 13 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 12 14 16 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 13 14 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp
  exact sub_eq_zero.mp hs

/-- In particular the nondegeneracy condition fails already on a finite
K₄-free graph, in every vector space over F₃. -/
theorem no_assignment (f : Fin 17 → Fin 17 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      triangleSum f a b c = 0)
    (hne : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      f a b ≠ f a c) : False := by
  exact hne 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (collapse f h)

#print axioms collapse
#print axioms no_assignment
end Erdos595F3Obstruction
