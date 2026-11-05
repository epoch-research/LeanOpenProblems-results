import Submission.DivisorAverage

/-!
# Real cutoffs for normalized divisor sums

The normalization at a real cutoff is equivalent to the normalization at its
natural floor. In particular, the original divisor asymptotic applies to the
polynomial `X`. These are supporting results only.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology Asymptotics

lemma tendsto_floor_mul_log_div :
    Tendsto (fun x : ℝ ↦ ((Nat.floor x : ℝ) * Real.log (Nat.floor x : ℝ)) /
        (x * Real.log x)) atTop (𝓝 1) := by
  have hfloor : (fun x : ℝ ↦ (Nat.floor x : ℝ)) ~[atTop] (fun x ↦ x) :=
    Asymptotics.isEquivalent_nat_floor
  have heq := hfloor.mul (hfloor.log tendsto_id)
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp heq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact mul_ne_zero (ne_of_gt (zero_lt_one.trans hx)) (ne_of_gt (Real.log_pos hx))

/-- Transfer any natural-cutoff `N * log N` limit to a real cutoff. -/
lemma tendsto_floor_normalization {A : ℕ → ℝ} {c : ℝ}
    (hA : Tendsto (fun N : ℕ ↦ A N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 c)) :
    Tendsto (fun x : ℝ ↦ A (Nat.floor x) / (x * Real.log x)) atTop (𝓝 c) := by
  have h := (hA.comp tendsto_nat_floor_atTop).mul tendsto_floor_mul_log_div
  simp only [Function.comp_apply, mul_one] at h
  apply h.congr'
  filter_upwards [tendsto_nat_floor_atTop.eventually (eventually_ge_atTop 2)] with x hx
  have hN1 : (1 : ℝ) < (Nat.floor x : ℝ) := by
    exact_mod_cast (show 1 < Nat.floor x by omega)
  have hNz : (Nat.floor x : ℝ) * Real.log (Nat.floor x : ℝ) ≠ 0 :=
    mul_ne_zero (ne_of_gt (zero_lt_one.trans hN1)) (ne_of_gt (Real.log_pos hN1))
  exact div_mul_div_cancel₀ hNz

/-- Natural and real cutoffs give equivalent normalized limits. -/
lemma tendsto_floor_normalization_iff {A : ℕ → ℝ} {c : ℝ} :
    Tendsto (fun N : ℕ ↦ A N / ((N : ℝ) * Real.log (N : ℝ)))
        atTop (𝓝 c) ↔
      Tendsto (fun x : ℝ ↦ A (Nat.floor x) / (x * Real.log x)) atTop (𝓝 c) := by
  constructor
  · exact tendsto_floor_normalization
  · intro h
    simpa only [Function.comp_def, Nat.floor_natCast] using
      h.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)

/-- The defining divisor-average limit is one for `f = X`. -/
theorem tendsto_X_average :
    Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor ((X : ℤ[X]).eval (n : ℤ))) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 1) := by
  simpa only [divisorSummatory, eval_X, Nat.floor_natCast] using
    tendsto_floor_normalization tendsto_divisorSummatory_div_mul_log

/-- `X` satisfies all the polynomial hypotheses in the conjecture. -/
theorem X_admissible :
    (X : ℤ[X]).natDegree ≠ 0 ∧ Irreducible (X : ℤ[X]) ∧
      (∀ᶠ n : ℤ in atTop, 1 ≤ (X : ℤ[X]).eval n) := by
  refine ⟨by simp, irreducible_X, ?_⟩
  simpa only [eval_X] using eventually_ge_atTop (1 : ℤ)

end Erdos975Support
