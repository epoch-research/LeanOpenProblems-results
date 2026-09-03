import Submission.LogLogMomentLower

/-!
# Coefficient comparisons for the near-moment construction

These are upper bounds on the explicit lower certificates, NOT on the
shifted-prime moments themselves. They show that the same finite conditions
used for the lower bounds prevent a growing order from compensating for
their coefficient loss.
-/

open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma nearMoment_order_le_scale (w A m : ℕ)
    (hR : nearMomentR w A m+1 ≤ logMomentScale m) :
    w+1 ≤ logMomentScale m := by
  have h : w ≤ nearMomentR w A m := by
    unfold nearMomentR nearMomentC
    calc
      w ≤ 4096*w := Nat.le_mul_of_pos_left _ (by decide)
      _ ≤ 4096*w*(A+20) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  omega

lemma half_factorial_lt_eighth_power (w : ℕ) (hw : 1 ≤ w)
    (E : ℝ) (hE : 2 ≤ E) (horder : (w+1 : ℕ) ≤ E^2) :
    (2 : ℝ)^(w+1)*((w+1).factorial : ℝ) < E^(8*w) := by
  have hE0 : 0 ≤ E := by linarith
  have hE1 : 1 < E := by linarith
  have hfact : ((w+1).factorial : ℝ) ≤ E^(2*(w+1)) := by
    calc
      _ ≤ ((w+1 : ℕ) : ℝ)^(w+1) := by exact_mod_cast Nat.factorial_le_pow (w+1)
      _ ≤ (E^2)^(w+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) horder _
      _ = _ := (pow_mul _ _ _).symm
  calc
    _ ≤ E^(w+1)*E^(2*(w+1)) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) hE _) hfact
        (Nat.cast_nonneg _) (pow_nonneg hE0 _)
    _ = E^(3*(w+1)) := by rw [← pow_add]; congr 1; omega
    _ ≤ E^(6*w) := pow_le_pow_right₀ hE1.le (by omega)
    _ < E^(8*w) := pow_lt_pow_right₀ hE1 (by omega)

lemma coefficient_lt_half_geometric_of_cross (w : ℕ) (Z B : ℝ)
    (hB : 0 < B)
    (hcross : Z*((2 : ℝ)^(w+1)*((w+1).factorial : ℝ)) < B) :
    Z/B < (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) := by
  have hf : (0 : ℝ) < (w+1).factorial := by exact_mod_cast Nat.factorial_pos (w+1)
  have htwo : (0 : ℝ) < (2 : ℝ)^(w+1) := by positivity
  apply (div_lt_div_iff₀ hB hf).mpr
  apply (mul_lt_mul_iff_right₀ htwo).mp
  have he : (1/2 : ℝ)^(w+1)*(2 : ℝ)^(w+1) = 1 := by
    rw [← mul_pow]; norm_num
  calc
    (2 : ℝ)^(w+1)*(Z*((w+1).factorial : ℝ)) =
        Z*((2 : ℝ)^(w+1)*((w+1).factorial : ℝ)) := by ring
    _ < B := hcross
    _ = (2 : ℝ)^(w+1)*((1/2 : ℝ)^(w+1)*B) := by
      calc
        B = ((1/2 : ℝ)^(w+1)*(2 : ℝ)^(w+1))*B := by rw [he,one_mul]
        _ = _ := by ring

lemma log_nearMomentX_lower_power (w A m : ℕ) (hw : 1 ≤ w) :
    (logMomentScale m : ℝ)^(A+20) ≤ Real.log (nearMomentX w A m : ℝ) := by
  let E := logMomentScale m
  have hE : 0 < E := lt_of_lt_of_le (by decide : 0 < 32) (logMomentScale_ge m)
  have hR : 0 < nearMomentR w A m := nearMomentR_pos w A m hw
  have hs : E^(A+20) ≤ nearMomentT w A m*E := by
    have h := Nat.le_mul_of_pos_left (E^(A+20))
      (show 0 < 64*nearMomentR w A m*E by positivity)
    change E^(A+20) ≤ (64*nearMomentR w A m*E^(A+20))*E
    nlinarith only [h]
  exact (by exact_mod_cast hs : (E : ℝ)^(A+20) ≤ (nearMomentT w A m*E : ℕ)).trans
    (log_progression_scale_ge _)

/-- At every admissible order and scale, the raw near-moment coefficient is
strictly below even the half-geometric factorial coefficient. -/
theorem nearMoment_raw_coefficient_gap (w A m : ℕ) (hw : 1 ≤ w)
    (hR : nearMomentR w A m+1 ≤ logMomentScale m) :
    (logMomentScale m : ℝ)^(w*(A+8)) /
      (Real.log (nearMomentX w A m : ℝ))^w <
        (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) := by
  let E := logMomentScale m
  let B := Real.log (nearMomentX w A m : ℝ)
  let Z : ℝ := (E : ℝ)^(w*(A+8))
  have hE : (2 : ℝ) ≤ E := by exact_mod_cast (show 2 ≤ E by have := logMomentScale_ge m; omega)
  have hE0 : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have horder : (w+1 : ℕ) ≤ (E : ℝ)^2 := by
    have h := nearMoment_order_le_scale w A m hR
    have h' : ((w+1 : ℕ) : ℝ) ≤ E := by exact_mod_cast h
    nlinarith
  have hf := half_factorial_lt_eighth_power w hw E hE horder
  have hB : 0 < B := lt_of_lt_of_le (by norm_num)
    (one_le_log_nearMomentX w A m hw)
  have hZ : 0 < Z := pow_pos hE0 _
  apply coefficient_lt_half_geometric_of_cross w Z (B^w) (pow_pos hB _)
  calc
    _ < Z*(E : ℝ)^(8*w) := mul_lt_mul_of_pos_left hf hZ
    _ = (E : ℝ)^(w*(A+16)) := by
      dsimp [Z]
      rw [← pow_add]
      apply congrArg (fun n : ℕ => (E : ℝ)^n)
      ring
    _ ≤ (E : ℝ)^(w*(A+20)) := pow_le_pow_right₀ hE1 (Nat.mul_le_mul_left w (by omega))
    _ ≤ B^w := by
      have h := pow_le_pow_left₀ (show 0 ≤ (E : ℝ)^(A+20) by positivity)
        (log_nearMomentX_lower_power w A m hw) w
      rw [← pow_mul] at h
      simpa only [mul_comm (A+20) w] using h

/-- The displayed log-log-loss coefficient has the same obstruction,
uniformly over all orders satisfying the finite R condition. -/
theorem loglogMoment_coefficient_gap (w m : ℕ) (hw : 1 ≤ w) (hm : 32 ≤ m)
    (hR : nearMomentR w (loglogMomentA m) (loglogMomentIndex m)+1 ≤ loglogMomentE m) :
    (1 : ℝ)/(Real.log (Real.log (loglogMomentX w m : ℝ)))^(30*w) <
      (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) := by
  let H := Real.log (Real.log (loglogMomentX w m : ℝ))
  have hA : (1 : ℝ) ≤ loglogMomentA m := by exact_mod_cast loglogMomentA_pos m
  have hH0 := loglogMoment_log_log_lower w m hw hm
  have hH : 2 ≤ H := by change 32*(loglogMomentA m : ℝ) ≤ H at hH0; linarith
  have hHpos : 0 < H := by linarith
  have horder : (w+1 : ℕ) ≤ H^2 := by
    have h := nearMoment_order_le_scale w (loglogMomentA m) (loglogMomentIndex m) hR
    have h' : ((w+1 : ℕ) : ℝ) ≤ loglogMomentE m := by exact_mod_cast h
    exact h'.trans (loglogMomentE_le_log_log_sq w m hw hm)
  apply coefficient_lt_half_geometric_of_cross w 1 (H^(30*w)) (pow_pos hHpos _)
  rw [one_mul]
  exact (half_factorial_lt_eighth_power w hw H hH horder).trans_le
    (pow_le_pow_right₀ (by linarith) (by omega))

end Erdos821
