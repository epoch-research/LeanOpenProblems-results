import Submission.ReversalInvariantArcColoring
import Submission.LocallyFiniteFolkmanTarget

/-!
A single countable K4-free source already has no finite reversal-invariant
weak arc-triangle coloring, while it has both a countable invariant coloring
and an anti-invariant weak two-coloring. Thus unbounded finite palette
requirements do not cross the countable-palette gap in this formulation.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ReversalInvariantFiniteGap
open Erdos595ArcAdjoint Erdos595Work Erdos595ReversalInvariantArcColoring
open Erdos595FinitePalette

variable {V C : Type*}

lemma coloring_of_injective (G : SimpleGraph V) (c : Sym2 V → C)
    (hc : Function.Injective c) : HasColoring G C := by
  refine ⟨c, ?_⟩
  intro a b t hab hat hbt he
  rcases Sym2.eq_iff.mp (hc he.1) with ⟨_,h⟩ | ⟨h,_⟩
  · exact hbt.ne h
  · exact hat.ne h

lemma countable_invariant [Countable V] (G : SimpleGraph V) :
    ∃ c : Arc G → ℕ, (∀ e, c (rev G e) = c e) ∧ Valid G c := by
  obtain ⟨c,hc⟩ := exists_injective_nat (Sym2 V)
  exact (palette_iff G).mp (coloring_of_injective G c hc)

open Erdos595LocallyFiniteFolkmanTarget (Carrier H)

lemma carrier_infinite : Infinite Carrier := by
  apply not_finite_iff_infinite.mp
  intro h
  letI := h
  exact Erdos595LocallyFiniteFolkmanTarget.no_finite_palette (Sym2 Carrier)
    (coloring_of_injective H id Function.injective_id)

lemma no_finite_invariant (C : Type) [Finite C] [Nonempty C] :
    ¬∃ c : Arc H → C, (∀ e, c (rev H e) = c e) ∧ Valid H c := by
  intro h
  exact Erdos595LocallyFiniteFolkmanTarget.no_finite_palette C ((palette_iff H).mpr h)

/-- The finite-versus-countable distinction persists even for one countable,
locally finite, K4-free source. This source is NOT a witness for Erdős 595. -/
theorem finite_countable_gap :
    ∃ (V : Type) (_ : Countable V) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧
      (∃ c : Arc G → Bool, (∀ e, c (rev G e) ≠ c e) ∧ Valid G c) ∧
      (∀ n : ℕ, ¬∃ c : Arc G → Fin (n+1),
        (∀ e, c (rev G e) = c e) ∧ Valid G c) ∧
      (∃ c : Arc G → ℕ, (∀ e, c (rev G e) = c e) ∧ Valid G c) := by
  refine ⟨Carrier, inferInstance, carrier_infinite, H,
    Erdos595LocallyFiniteFolkmanTarget.cliqueFree,
    anti_invariant_two_coloring H, ?_, countable_invariant H⟩
  intro n
  exact no_finite_invariant (Fin (n+1))

#print axioms carrier_infinite
#print axioms no_finite_invariant
#print axioms finite_countable_gap
end Erdos595ReversalInvariantFiniteGap
