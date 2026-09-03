import Submission.BuchstabEulerQuadrature
import Submission.BuchstabDefectCoordinates
import Submission.BuchstabLowerTail

/-! Exact one-step main-term comparisons in shifted Euler coordinates.
The child-profile hypotheses are explicit; this file does not assume or
assert recursive domination. All square guards and all primes are retained. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Set Finset MeasureTheory Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 1800000

lemma euler_shifted_child_ge (C B s : ℝ) (hC : 0 < C) (hs : 0 ≤ s)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (k i : ℕ) (hi : i ≤ k) :
    s-1 ≤ (s*eulerCoordinate C k+B-log (nthPrime i : ℝ))/eulerCoordinate C i := by
  have hT := eulerCoordinate_pos C hC
  have hm := div_le_div_of_nonneg_left (mul_nonneg hs (hT k).le) (hT i)
    (eulerCoordinate_monotone C hC hi)
  rw [mul_div_cancel_right₀ _ (hT k).ne'] at hm
  exact (sub_le_sub_right hm 1).trans (euler_shifted_child_coordinate C B s hC hB k i)

/-- A uniform upper child profile gives an exact lower main-term comparison
with one additive shift in log(D), rather than a quadrature remainder. -/
theorem referenceLower_euler_step (C B b : ℝ) (hC : 0 < C)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (hb : B ≤ b) (n : ℕ) (f : ℝ → ℝ)
    (hf : AntitoneOn f (Ici 1)) (hf0 : ∀ x, 1 ≤ x → 0 ≤ f x)
    (hfi : IntegrableOn f (Ioi 1))
    (hU : ∀ k : ℕ, ∀ t : ℝ, 1 ≤ t →
      referenceUpper n k (exp (t*eulerCoordinate C k+b)) ≤
        prefixDensity primeMarginal k*(1+f t))
    (k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    prefixDensity primeMarginal k*(1-tailIntegral f (s-1)/s) ≤
      referenceLower n k (exp (s*eulerCoordinate C k+b+B)) := by
  have hs0 : 0 < s := by linarith
  have hkeep : primeKeep nthPrime k (exp (s*eulerCoordinate C k+b+B)) := by
    simpa only [add_assoc] using
      eulerCoordinate_square_guard C B (b+B) s hC hB (by linarith) hs k
  apply lowerStep_ge_of_excess _ _ _ _ _ _ hkeep
  change (∑ i : Fin k, primeMarginal i.val*(referenceUpper n i.val
    (exp (s*eulerCoordinate C k+b+B)*primeMarginal i.val)-prefixDensity primeMarginal i.val)) ≤ _
  have hsum : (∑ i : Fin k, primeMarginal i.val*(referenceUpper n i.val
      (exp (s*eulerCoordinate C k+b+B)*primeMarginal i.val)-prefixDensity primeMarginal i.val)) ≤
      (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*
        f ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)) := by
    apply sum_le_sum
    intro i hi
    have ht := euler_shifted_child_ge C B s hC hs0.le hB k i.val i.isLt.le
    have hh := hU i.val ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)
      (by linarith only [ht,hs])
    rw [euler_shifted_child_level C B b s hC k i.val]
    have hh' : referenceUpper n i.val
        (exp (((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)*
          eulerCoordinate C i.val+b))-prefixDensity primeMarginal i.val ≤
        prefixDensity primeMarginal i.val*
          f ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val) := by
      linarith only [hh]
    exact (mul_le_mul_of_nonneg_left hh' (primeMarginal_pos i.val).le).trans_eq (by ring)
  have hquad := euler_shifted_profile_sum C B s hC hs0 hB k f
    (hf.mono (Ici_subset_Ici.mpr (by linarith)))
    (fun x hx => hf0 x (by linarith only [hx,hs]))
    (hfi.mono_set (Ioi_subset_Ioi (by linarith)))
  exact (hsum.trans hquad).trans_eq (by ring)

/-- Uniform lower child deficits give the corresponding exact upper step.
The profile below level two must already contain the square-cutoff deficit. -/
theorem referenceUpper_euler_step (C B b : ℝ) (hC : 0 < C)
    (hB : ∀ i : ℕ, |eulerCoordinate C i-log (nthPrime i : ℝ)| ≤ B)
    (n : ℕ) (f : ℝ → ℝ)
    (hf : AntitoneOn f (Ici 0)) (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hfi : IntegrableOn f (Ioi 0))
    (hL : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      prefixDensity primeMarginal k*(1-f t) ≤
        referenceLower n k (exp (t*eulerCoordinate C k+b)))
    (k : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    referenceUpper (n+1) k (exp (s*eulerCoordinate C k+b+B)) ≤
      prefixDensity primeMarginal k*(1+tailIntegral f (s-1)/s) := by
  have hs0 : 0 < s := by linarith
  apply upperMain_le_of_deficit _ _ _ n
  change (∑ i : Fin k, primeMarginal i.val*(prefixDensity primeMarginal i.val-
    referenceLower n i.val (exp (s*eulerCoordinate C k+b+B)*primeMarginal i.val))) ≤ _
  have hsum : (∑ i : Fin k, primeMarginal i.val*(prefixDensity primeMarginal i.val-
      referenceLower n i.val (exp (s*eulerCoordinate C k+b+B)*primeMarginal i.val))) ≤
      (∑ i : Fin k, primeMarginal i.val*prefixDensity primeMarginal i.val*
        f ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)) := by
    apply sum_le_sum
    intro i hi
    have ht := euler_shifted_child_ge C B s hC hs0.le hB k i.val i.isLt.le
    have hh := hL i.val ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)
      (by linarith only [ht,hs])
    rw [euler_shifted_child_level C B b s hC k i.val]
    have hh' : prefixDensity primeMarginal i.val-referenceLower n i.val
        (exp (((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val)*
          eulerCoordinate C i.val+b)) ≤ prefixDensity primeMarginal i.val*
          f ((s*eulerCoordinate C k+B-log (nthPrime i.val : ℝ))/eulerCoordinate C i.val) := by
      linarith only [hh]
    exact (mul_le_mul_of_nonneg_left hh' (primeMarginal_pos i.val).le).trans_eq (by ring)
  have hquad := euler_shifted_profile_sum C B s hC hs0 hB k f
    (hf.mono (Ici_subset_Ici.mpr (by linarith)))
    (fun x hx => hf0 x (by linarith only [hx,hs]))
    (hfi.mono_set (Ioi_subset_Ioi (by linarith)))
  exact (hsum.trans hquad).trans_eq (by ring)

#print axioms referenceLower_euler_step
#print axioms referenceUpper_euler_step
end Erdos970.RecursiveSieve.Buchstab
