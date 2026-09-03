import Submission.FirstHitSaturatedSurvivor
import Submission.FirstHitRefinedLogPower

/-! An unrestricted k^(54/25) log(k+2)^(104/25) bound from cubic saturation
and the eighth-power far tail. The quadratic conjecture remains open here. -/
namespace Erdos970.FiniteSelberg
open Finset Real

/-- An unrestricted bound with no auxiliary positive power slack. -/
theorem exists_saturatedHit_logpower_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤
      C * (k : ℝ) ^ (54 / 25 : ℝ) * log ((k : ℝ) + 2) ^ (104 / 25 : ℝ) := by
  obtain ⟨L₀, hL₀, hmain⟩ := exists_saturatedHitMainSum_slack
  let K : ℝ := 2 * (1 + L₀) + 362
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨1001 * K ^ 2 * exp L₀ * (160 : ℝ) ^ (54 / 25 : ℝ), by positivity, ?_⟩
  intro k hk
  let p := Nat.nth Nat.Prime k
  let t := log ((k : ℝ) + 2)
  have hp := Nat.prime_nth_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog2 : log (2 : ℝ) ≤ t := log_le_log (by norm_num) (by linarith)
  have ht : (1 / 2 : ℝ) ≤ t := by linarith [log_two_gt_d9]
  have ht0 : 0 < t := by linarith
  let L : ℝ := L₀ + (54 / 25 : ℝ) * log (p : ℝ)
  have hLL : L₀ ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := hL₀.trans_le hLL
  have hLp := nth_prime_log_bound k hk
  have hLupper : 1 + L ≤ K * t := by
    change log (p : ℝ) ≤ 160 * t at hLp
    have hbase : 1 + L₀ ≤ 2 * (1 + L₀) * t := by nlinarith
    dsimp only [L, K]
    nlinarith only [hbase, hLp, ht0]
  let X : ℝ := 1000 * (1 + L) ^ 2 * exp L
  let m : ℕ := ⌊X⌋₊ + 1
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one X
  have hm : 200 * L * (1 + 4 * exp L * (1 + L)) < (m : ℝ) :=
    (refinedHit_remainder_log_bound L hL.le).trans_lt hXm
  have hpZ : p ≤ saturatedHitPrimeCut L 0 := by
    have hex : (p : ℝ) ≤ exp (L / (2 * saturatedHitNode 0 + 1)) := by
      calc
        (p : ℝ) = exp (log (p : ℝ)) := (exp_log hp0).symm
        _ ≤ exp (L / (2 * saturatedHitNode 0 + 1)) := by
          apply exp_le_exp.mpr
          norm_num [saturatedHitNode, L]
          linarith
    exact Nat.le_floor hex
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_saturatedHitMainSum k L hL m hpZ (hmain L hLL) hm)
  have hmupper : (m : ℝ) ≤ X + 1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have hunit : 1 ≤ (1 + L) ^ 2 * exp L := by
    have he := one_le_exp hL.le
    have hsq : 1 ≤ (1 + L) ^ 2 := by nlinarith
    nlinarith only [mul_le_mul hsq he (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (1 + L))]
  have hupper : (jacobsthalFunction k : ℝ) ≤ 1001 * (1 + L) ^ 2 * exp L := by
    have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [X] at hmupper
    nlinarith only [hjR, hmupper, hunit]
  have hpowbase : (p : ℝ) ≤ 160 * (k : ℝ) * t := by
    have hh := PrimeCountingLower.nth_prime_mul_log k
    change (p : ℝ) ≤ 80 * ((k : ℝ) + 1) * t at hh
    have hh' := mul_le_mul_of_nonneg_right (show 80 * ((k : ℝ) + 1) ≤ 160 * k by linarith) ht0.le
    exact hh.trans hh'
  have hpow := rpow_le_rpow hp0.le hpowbase (by norm_num : (0 : ℝ) ≤ 54 / 25)
  have heq : exp L = exp L₀ * (p : ℝ) ^ (54 / 25 : ℝ) := by
    rw [rpow_def_of_pos hp0, ← exp_add]
    congr 1
    dsimp [L]
    ring
  have heupper : exp L ≤ exp L₀ * (160 * (k : ℝ) * t) ^ (54 / 25 : ℝ) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpow (exp_pos _).le
  have hs := pow_le_pow_left₀ (show 0 ≤ 1 + L by linarith) hLupper 2
  calc
    (jacobsthalFunction k : ℝ) ≤ 1001 * (1 + L) ^ 2 * exp L := hupper
    _ ≤ 1001 * (K * t) ^ 2 * (exp L₀ * (160 * (k : ℝ) * t) ^ (54 / 25 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) heupper (exp_pos _).le (by positivity)
    _ = (1001 * K ^ 2 * exp L₀ * (160 : ℝ) ^ (54 / 25 : ℝ)) *
        (k : ℝ) ^ (54 / 25 : ℝ) * t ^ (104 / 25 : ℝ) := by
      rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160 * k) ht0.le,
        mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le,
        show (104 / 25 : ℝ) = 2 + 54 / 25 by norm_num, rpow_add ht0, rpow_two]
      ring

/-- The first-hit base exponent is 54/25, with any positive power allowance.
The constant depends on that allowance; no quadratic estimate follows by
letting the allowance tend to zero. -/
theorem exists_saturatedHit_power_bound_any (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * (k : ℝ) ^ ((54 / 25 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_saturatedHit_logpower_bound
  let D : ℝ := ((3 : ℝ) ^ (ε / (104 / 25)) / (ε / (104 / 25))) ^ (104 / 25 : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl := log_rpow_le_small_power (104 / 25) ε (by norm_num) hε k hk
  change log ((k : ℝ) + 2) ^ (104 / 25 : ℝ) ≤ D * (k : ℝ) ^ ε at hl
  have hh := (hbound k hk).trans (mul_le_mul_of_nonneg_left hl
    (show 0 ≤ C * (k : ℝ) ^ (54 / 25 : ℝ) by positivity))
  rw [rpow_add hk0]
  convert hh using 1 <;> ring

#print axioms exists_saturatedHit_logpower_bound
#print axioms exists_saturatedHit_power_bound_any
end Erdos970.FiniteSelberg
