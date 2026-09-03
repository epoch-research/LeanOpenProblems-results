import Submission.FirstPowerArity
import Submission.InverseTotientMoments

/-!
# Bounded first-power arity cannot provide a subcritical second-moment divergence

Every fixed arity has a convergent second moment above one half. This applies
in particular to the semiprime collision construction in PrimeRectangles.
It makes no assertion about inputs with unbounded first-power arity.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

lemma gFirstPowerAtMost_le_g (r n : ℕ) : gFirstPowerAtMost r n ≤ g n :=
  Set.ncard_le_ncard (fun _ hm => hm.1) (finite_totient_fiber n)

theorem summable_fixed_arity_second_moment (r : ℕ) (s : ℝ) (hs : 1/2 < s) :
    Summable (fun n : ℕ => (gFirstPowerAtMost r n : ℝ)^2 * (n : ℝ)^(-(2*s))) := by
  let δ := s-1/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have Hu : 1 < 2*s-δ := by dsimp [δ]; linarith
  apply (summable_inverse_totient_first_moment (2*s-δ) Hu).of_norm_bounded_eventually_nat
  filter_upwards [eventually_gFirstPowerAtMost_le_rpow r δ hδ,
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hle : (gFirstPowerAtMost r n : ℝ) ≤ (g n : ℝ) := by
    exact_mod_cast gFirstPowerAtMost_le_g r n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (gFirstPowerAtMost r n : ℝ)^2 * (n : ℝ)^(-(2*s)) =
        (gFirstPowerAtMost r n : ℝ) *
          ((gFirstPowerAtMost r n : ℝ)*(n : ℝ)^(-(2*s))) := by ring
    _ ≤ (g n : ℝ)*((n : ℝ)^δ*(n : ℝ)^(-(2*s))) :=
      mul_le_mul hle
        (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnpos.le _))
        (by positivity) (Nat.cast_nonneg _)
    _ = (g n : ℝ)*(n : ℝ)^(-(2*s-δ)) := by
      rw [← Real.rpow_add hnpos]
      congr 2
      ring

end Erdos821
