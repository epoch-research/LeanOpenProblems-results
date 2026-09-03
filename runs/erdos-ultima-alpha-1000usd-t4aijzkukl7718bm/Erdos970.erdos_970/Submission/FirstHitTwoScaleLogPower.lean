import Submission.FirstHitTwoScaleSurvivor
import Submission.FirstHitRefinedLogPower

/-! Two logarithmic powers saved in the unrestricted first-hit bound.
The base exponent remains 54/25 > 2, so the original conjecture is not settled. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma twoScale_remainder_bound (L : ℝ) (hL : 0 < L) :
    400*L*(1+twoScaleCostConstant*exp L/L^2) ≤
      400*(2+twoScaleCostConstant)*exp L/L := by
  have hh := quadratic_le_exp_of_nonneg hL.le
  have hsq : L^2 ≤ 2*exp L := by nlinarith
  apply (mul_le_mul_iff_left₀ hL).mp
  field_simp
  nlinarith

/-- Unrestricted, with one fixed real constant for every positive budget. -/
theorem exists_twoScale_logpower_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(54/25 : ℝ)*log ((k : ℝ)+2)^(29/25 : ℝ) := by
  obtain ⟨L₀,hL₀,hmain⟩ := exists_twoScaleMainSum_slack
  let A := twoScaleCostConstant
  have hA : 0 < A := twoScaleCostConstant_pos
  refine ⟨401*(2+A)*exp L₀*(160 : ℝ)^(54/25 : ℝ), by positivity, ?_⟩
  intro k hk
  let p := Nat.nth Nat.Prime k
  let t := log ((k : ℝ)+2)
  have hp := Nat.prime_nth_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpN : k+2 ≤ p := by
    simpa only [Nat.nth_prime_zero_eq_two,Nat.add_zero] using
      (Nat.nth_strictMono Nat.infinite_setOf_prime).add_le_nat k 0
  have ht0 : 0 < t := log_pos (by linarith)
  have htp : t ≤ log (p : ℝ) := log_le_log (by positivity)
    (by exact_mod_cast hpN)
  have hlp : 0 ≤ log (p : ℝ) := (ht0.trans_le htp).le
  let L : ℝ := L₀+(54/25 : ℝ)*log (p : ℝ)
  have hLL : L₀ ≤ L := by dsimp [L]; linarith
  have hL100 : 100 ≤ L := hL₀.trans hLL
  have hL : 0 < L := by linarith
  have htL : t ≤ L := by dsimp [L]; linarith
  let X : ℝ := 400*(2+A)*exp L/L
  let m : ℕ := ⌊X⌋₊+1
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by
    simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hm : 400*L*(1+twoScaleCostConstant*exp L/L^2) < (m : ℝ) :=
    (twoScale_remainder_bound L hL).trans_lt hXm
  have hpZ : p ≤ saturatedHitPrimeCut L 0 := by
    have hex : (p : ℝ) ≤ exp (L/(2*saturatedHitNode 0+1)) := by
      calc
        (p : ℝ) = exp (log (p : ℝ)) := (exp_log hp0).symm
        _ ≤ exp (L/(2*saturatedHitNode 0+1)) := by
          apply exp_le_exp.mpr
          norm_num [saturatedHitNode,L]
          linarith
    exact Nat.le_floor hex
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_twoScale k L hL100 m hpZ (hmain L hLL) hm)
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have heL : 1 ≤ exp L/L := (le_div_iff₀ hL).mpr (by linarith [add_one_le_exp L])
  have hunit : 1 ≤ (2+A)*exp L/L := by
    have hh := mul_le_mul (show (1 : ℝ) ≤ 2+A by linarith) heL
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 2+A)
    simpa only [one_mul,mul_div_assoc] using hh
  have hupper : (jacobsthalFunction k : ℝ) ≤ 401*(2+A)*exp L/L := by
    have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [X] at hmupper
    have heq : 401*(2+A)*exp L/L = 400*(2+A)*exp L/L+(2+A)*exp L/L := by ring
    rw [heq]
    linarith
  have hpowbase : (p : ℝ) ≤ 160*(k : ℝ)*t := by
    have hh := PrimeCountingLower.nth_prime_mul_log k
    change (p : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
    have hh' := mul_le_mul_of_nonneg_right (show 80*((k : ℝ)+1) ≤ 160*k by linarith) ht0.le
    exact hh.trans hh'
  have hpow := rpow_le_rpow hp0.le hpowbase (by norm_num : (0 : ℝ) ≤ 54/25)
  have heq : exp L = exp L₀*(p : ℝ)^(54/25 : ℝ) := by
    rw [rpow_def_of_pos hp0, ← exp_add]
    congr 1
    dsimp [L]
    ring
  have heupper : exp L ≤ exp L₀*(160*(k : ℝ)*t)^(54/25 : ℝ) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpow (exp_pos _).le
  calc
    (jacobsthalFunction k : ℝ) ≤ 401*(2+A)*exp L/L := hupper
    _ ≤ 401*(2+A)*exp L/t := div_le_div_of_nonneg_left (by positivity) ht0 htL
    _ ≤ 401*(2+A)*(exp L₀*(160*(k : ℝ)*t)^(54/25 : ℝ))/t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left heupper (by positivity)) ht0.le
    _ = (401*(2+A)*exp L₀*(160 : ℝ)^(54/25 : ℝ))*
        (k : ℝ)^(54/25 : ℝ)*t^(29/25 : ℝ) := by
      rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht0.le,
        mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le,
        show (29/25 : ℝ) = 54/25-1 by norm_num, rpow_sub ht0, rpow_one]
      ring

#print axioms exists_twoScale_logpower_bound
end Erdos970.FiniteSelberg
