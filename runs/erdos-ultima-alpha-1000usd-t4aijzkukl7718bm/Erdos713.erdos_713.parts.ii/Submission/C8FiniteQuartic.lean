import FormalConjecturesUtil
import Submission.C8QuarticAdditive

/-! Every quartic two-variable potential in the auxiliary incidence model
contains C8 over a finite characteristic-two field of order greater than eight.
This is a construction obstruction, not a proof or disproof of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8FiniteQuartic
open Erdos713C8FiniteQuadratic Erdos713C8QuarticMixed
open Erdos713C8QuarticEven Erdos713C8QuarticAdditive
variable {K : Type*} [Field K]

/-- All fifteen coefficients, including the constant term, are arbitrary. -/
theorem quartic_octagon_char_two [Fintype K] [CharP K 2]
    (A B C D E F G H I J L M N O P : K) (hq : 8 < Fintype.card K) :
    Octagon (quartic A B C D E F G H I J L M N O P) := by
  by_cases hBD : B ≠ 0 ∨ D ≠ 0
  · exact quartic_odd_mixed_octagon A B C D E F G H I J L M N O P (by omega) hBD
  · push_neg at hBD
    rcases hBD with ⟨rfl,rfl⟩
    by_cases hCubic : C ≠ 0 ∨ F ≠ 0 ∨ G ≠ 0 ∨ H ≠ 0 ∨ I ≠ 0
    · exact even_quartic_nonadditive A C E F G H I J L M N O P hCubic (by omega)
    · push_neg at hCubic
      rcases hCubic with ⟨rfl,rfl,rfl,rfl,rfl⟩
      exact additive_quartic_octagon A E J L M N O P hq

/-- The full graph has an injective copy, not just a closed walk. -/
theorem contains_quartic_char_two [Fintype K] [CharP K 2]
    (A B C D E F G H I J L M N O P : K) (hq : 8 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (quartic A B C D E F G H I J L M N O P) :=
  contains_of_octagon (quartic_octagon_char_two A B C D E F G H I J L M N O P hq)

#print axioms quartic_octagon_char_two
#print axioms contains_quartic_char_two
end Erdos713C8FiniteQuartic
