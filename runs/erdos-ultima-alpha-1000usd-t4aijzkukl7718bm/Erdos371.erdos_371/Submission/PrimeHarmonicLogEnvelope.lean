import Submission.PrimeLoserCollisionBound

/-! A coarse real-logarithmic envelope for the elementary prime-harmonic
bound. Constants are chosen for convenience rather than sharpness. -/
namespace Erdos371.FiniteSieve
open Finset

lemma nat_log_two_le_two_log_add_one (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ 2*Real.log (n+1 : ℝ) := by
  have h₁ : (Nat.log 2 n : ℝ) ≤ Nat.log 2 (n+1) := by
    exact_mod_cast Nat.log_mono_right (Nat.le_succ n)
  have h₂ := Real.natLog_le_logb (n+1) 2
  simp only [Real.logb,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h₂
  have hlog : 0 ≤ Real.log (n+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hlog2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh : Real.log (n+1 : ℝ)/Real.log 2 ≤ 2*Real.log (n+1 : ℝ) := by
    apply (div_le_iff₀ hlog2).mpr
    have ht : 1 ≤ 2*Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [mul_le_mul_of_nonneg_right ht hlog]
  exact h₁.trans (h₂.trans hh)

lemma primeHarmonic_real_log_envelope (D : ℕ) :
    primeHarmonic D ≤ 48+24*Real.log (1+Real.log (D+1 : ℝ)) := by
  have hh := primeHarmonic_le_double_log D
  have h₁ := nat_log_two_le_two_log_add_one D
  have h₂ := nat_log_two_le_two_log_add_one (Nat.log 2 D)
  have hlogD : 0 ≤ Real.log (D+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hlog : Real.log (Nat.log 2 D+1 : ℝ) ≤ Real.log 2+Real.log (1+Real.log (D+1 : ℝ)) := by
    have ht : (Nat.log 2 D+1 : ℝ) ≤ 2*(1+Real.log (D+1 : ℝ)) := by linarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < Nat.log 2 D+1) ht
    rwa [Real.log_mul (by norm_num) (by positivity)] at hl
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  push_cast at hh
  linarith

lemma exp_three_primeHarmonic_real_log_bound (D : ℕ) :
    Real.exp (3*primeHarmonic D) ≤
      Real.exp 144*(1+Real.log (D+1 : ℝ))^72 := by
  have hbase : 0 < 1+Real.log (D+1 : ℝ) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ D+1 by norm_cast; omega)
    linarith
  calc
    _ ≤ Real.exp (144+72*Real.log (1+Real.log (D+1 : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith [primeHarmonic_real_log_envelope D])
    _ = _ := by
      rw [Real.exp_add]
      congr 1
      calc
        _ = (Real.exp (Real.log (1+Real.log (D+1 : ℝ))))^72 := by
          simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (1+Real.log (D+1 : ℝ))) 72
        _ = _ := by rw [Real.exp_log hbase]

lemma collision_primeHarmonic_weight_bound (X : ℕ) (hX : 1 ≤ X) :
    Real.exp (3*primeHarmonic (3+2*X^2))*(harmonic X : ℝ)^3 ≤
      (Real.exp 144*(6 : ℝ)^72)*(1+Real.log X)^75 := by
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogX := Real.log_nonneg hXr
  have hD : ((3+2*X^2+1 : ℕ) : ℝ) ≤ 6*(X : ℝ)^2 := by push_cast; nlinarith
  have hlogD : 1+Real.log (3+2*X^2+1 : ℝ) ≤ 6*(1+Real.log X) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (3+2*X^2+1 : ℕ)) hD
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
    have h6 : Real.log 6 ≤ 5 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<6)]
    push_cast at hh
    linarith
  have hpow : (1+Real.log (3+2*X^2+1 : ℝ))^72 ≤ (6 : ℝ)^72*(1+Real.log X)^72 := by
    have hbase : 0 ≤ 1+Real.log (3+2*X^2+1 : ℝ) := by
      have hh := Real.log_nonneg (show (1 : ℝ) ≤ 3+2*(X : ℝ)^2+1 by nlinarith [sq_nonneg (X : ℝ)])
      linarith
    simpa only [mul_pow] using pow_le_pow_left₀ hbase hlogD 72
  have hexp := exp_three_primeHarmonic_real_log_bound (3+2*X^2)
  push_cast at hexp
  have hexp' : Real.exp (3*primeHarmonic (3+2*X^2)) ≤
      (Real.exp 144*(6 : ℝ)^72)*(1+Real.log X)^72 := by
    exact hexp.trans (by convert mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg 144) using 1; ring)
  have hharm0 : (0 : ℝ) ≤ harmonic X := by
    exact_mod_cast (harmonic_pos (by omega : X ≠ 0)).le
  have hharm : (harmonic X : ℝ)^3 ≤ (1+Real.log X)^3 := by
    apply pow_le_pow_left₀ _ (harmonic_le_one_add_log X) 3
    exact hharm0
  have hmul := mul_le_mul hexp' hharm (by positivity : 0 ≤ (harmonic X : ℝ)^3)
    (by positivity : 0 ≤ (Real.exp 144*(6 : ℝ)^72)*(1+Real.log X)^72)
  convert hmul using 1
  ring

#print axioms primeHarmonic_real_log_envelope
#print axioms collision_primeHarmonic_weight_bound
end Erdos371.FiniteSieve
