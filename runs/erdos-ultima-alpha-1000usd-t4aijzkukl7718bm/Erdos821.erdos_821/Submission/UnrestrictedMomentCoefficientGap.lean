import Submission.NearMomentCoefficientGap

/-!
# A scale-formula obstruction without admissibility restrictions

The raw lower certificate in the near-moment construction stays below the
half-geometric factorial coefficient for every positive divisor order and
all parameters. No error-budget condition or order/scale restriction is
needed for this comparison. This bounds only the explicit certificate, NOT
the actual shifted-prime moment and NOT the conjectured multiplicity.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821
open AnalyticSieve HigherDivisors

lemma factorial_succ_le_two_pow_mul_self_pow (w : ℕ) :
    (w+1).factorial ≤ 2^w*w^w := by
  rw [Nat.factorial_succ]
  exact Nat.mul_le_mul Nat.lt_two_pow_self (Nat.factorial_le_pow w)

lemma half_factorial_lt_order_power (w : ℕ) (hw : 1 ≤ w) :
    (2 : ℝ)^(w+1)*((w+1).factorial : ℝ) < (16*(w : ℝ))^w := by
  have hfact : ((w+1).factorial : ℝ) ≤ (2 : ℝ)^w*(w : ℝ)^w := by
    exact_mod_cast factorial_succ_le_two_pow_mul_self_pow w
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  calc
    _ ≤ (2 : ℝ)^(w+1)*((2 : ℝ)^w*(w : ℝ)^w) :=
      mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = (2 : ℝ)^(2*w+1)*(w : ℝ)^w := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ < (2 : ℝ)^(4*w)*(w : ℝ)^w :=
      mul_lt_mul_of_pos_right
        (pow_lt_pow_right₀ (by norm_num) (by omega)) (pow_pos hwpos _)
    _ = _ := by
      rw [mul_pow, pow_mul]
      norm_num

lemma log_nearMomentX_ge_order_scale (w A m : ℕ) :
    16*(w : ℝ)*(logMomentScale m : ℝ)^(A+8) ≤
      Real.log (nearMomentX w A m : ℝ) := by
  let E := logMomentScale m
  have hE : 1 ≤ E := (by decide : 1 ≤ 32).trans (logMomentScale_ge m)
  have hR : w ≤ nearMomentR w A m := by
    unfold nearMomentR nearMomentC
    calc
      w ≤ 4096*w := Nat.le_mul_of_pos_left _ (by decide)
      _ ≤ 4096*w*(A+20) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hscale : 16*w*E^(A+8) ≤ nearMomentT w A m*E := by
    calc
      _ ≤ 64*nearMomentR w A m*E^(A+20) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by decide) hR)
          (Nat.pow_le_pow_right hE (by omega))
      _ ≤ (64*nearMomentR w A m*E^(A+20))*E := Nat.le_mul_of_pos_right _ hE
      _ = _ := rfl
  have hscaleR : 16*(w : ℝ)*(E : ℝ)^(A+8) ≤
      ((nearMomentT w A m*E : ℕ) : ℝ) := by exact_mod_cast hscale
  exact hscaleR.trans (log_progression_scale_ge _)

/-- The raw coefficient cannot reach even the half-geometric benchmark,
regardless of how the order and the two construction parameters are chosen. -/
theorem nearMoment_raw_coefficient_gap_unrestricted (w A m : ℕ) (hw : 1 ≤ w) :
    (logMomentScale m : ℝ)^(w*(A+8)) /
      (Real.log (nearMomentX w A m : ℝ))^w <
        (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) := by
  let E : ℝ := logMomentScale m
  let B : ℝ := Real.log (nearMomentX w A m : ℝ)
  let Z : ℝ := E^(w*(A+8))
  have hE : 0 < E := by
    dsimp [E]
    have h := logMomentScale_ge m
    exact_mod_cast (show 0 < logMomentScale m by omega)
  have hB : 0 < B := lt_of_lt_of_le (by norm_num)
    (one_le_log_nearMomentX w A m hw)
  have hZ : 0 < Z := pow_pos hE _
  apply coefficient_lt_half_geometric_of_cross w Z (B^w) (pow_pos hB _)
  calc
    _ < Z*(16*(w : ℝ))^w :=
      mul_lt_mul_of_pos_left (half_factorial_lt_order_power w hw) hZ
    _ = (16*(w : ℝ)*E^(A+8))^w := by
      simp only [Z, mul_pow, ← pow_mul]
      rw [mul_comm w (A+8)]
      ring
    _ ≤ B^w := pow_le_pow_left₀ (by positivity)
      (log_nearMomentX_ge_order_scale w A m) _

end Erdos821
