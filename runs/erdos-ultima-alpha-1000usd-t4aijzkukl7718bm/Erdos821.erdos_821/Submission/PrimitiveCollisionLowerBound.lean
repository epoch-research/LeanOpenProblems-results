import Submission.PrimitiveTotientCollisions
import Submission.CompositeMultiplicityGain

/-!
# An unconditional range of primitive collision divergence

The available fixed multiplicity exponent yields divergence among distinct,
coprime, squarefree totient pairs on a fixed interval above one half. This
does not extend the known exponent or establish divergence for every s < 1.
-/

open Nat Filter
open scoped Classical

namespace Erdos821
namespace PrimitiveCollisions

lemma not_summable_distinct_of_infinite_g_gt (s δ : ℝ) (hs : 1/2 < s) (hδ : 0 < δ)
    (H : {n : ℕ | (g n : ℝ) > (n : ℝ)^(s+δ)}.Infinite) :
    ¬Summable (fun p : Distinct => (Nat.totient p.val.val.val.1 : ℝ)^(-(2*s))) := by
  have Hsf := infinite_gSquarefree_gt_of_infinite_g_gt s δ (by linarith) hδ H
  have Hsf' : {n : ℕ | (n : ℝ)^s < (gSquarefree n : ℝ)}.Infinite :=
    Hsf.mono (fun n hn => hn.2)
  intro Hsum
  apply not_summable_square_moment_of_infinite (fun n => (gSquarefree n : ℝ)) s Hsf'
  exact (summable_squarefree_second_moment_iff s hs).mpr
    ((summable_primitive_iff_distinct s).mpr Hsum)

/-- The existing unconditional exponent supplies a nonempty, but fixed,
interval of primitive off-diagonal divergence above one half. -/
theorem not_summable_distinct_composite_range (s : ℝ) (hs : 1/2 < s)
    (hupper : s < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)) :
    ¬Summable (fun p : Distinct => (Nat.totient p.val.val.val.1 : ℝ)^(-(2*s))) := by
  let α := 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)
  have hgap : 0 < (α-s)/2 := by dsimp [α]; linarith
  apply not_summable_distinct_of_infinite_g_gt s ((α-s)/2) hs hgap
  apply infinite_g_gt_composite_uniform
  change s + (α-s)/2 < α
  linarith

/-- In particular, there are infinitely many ordered pairs of distinct,
coprime, squarefree inputs with equal totient. -/
theorem infinite_distinct_primitive_collisions : Infinite Distinct := by
  let G := 1/(80000000*Sieve.totientRatioAverageConstant+10)
  have hC := totientRatioAverageConstant_ge_one
  have hG : 0 < G := by dsimp [G]; positivity
  have H := not_summable_distinct_composite_range (1/2+G/2)
    (by linarith) (by change 1/2+G/2 < 1/2+G; linarith)
  by_contra h
  haveI : Finite Distinct := not_infinite_iff_finite.mp h
  exact H (summable_of_finite_support (Set.toFinite _))

end PrimitiveCollisions
end Erdos821
