import Submission.FirstHitNormalizedSurvivor
import Submission.FirstHitRefinedLogPower

/-! The normalizer-sensitive remainder removes the previous log-log factor.
The unrestricted exponent 54/25 is still larger than two: this does not
settle the original quadratic conjecture. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma normalizedFirstHit_remainder (L : ℝ) (hL : 0 ≤ L) :
    200*L*(1+normalizedFirstHitCostConstant*exp L) ≤
      200*(1+normalizedFirstHitCostConstant)*(1+L)*exp L := by
  have hA := normalizedFirstHitCostConstant_pos
  have hE := one_le_exp hL
  have hh := mul_le_mul_of_nonneg_left hE hL
  have hh' := mul_nonneg hL (mul_nonneg hA.le (exp_pos L).le)
  nlinarith

/-- An improved unrestricted bound. The exponent has not been rounded down
or replaced by the conjectured exponent two. -/
theorem exists_normalizedHit_logpower_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(54/25 : ℝ)*log ((k : ℝ)+2)^(79/25 : ℝ) := by
  obtain ⟨L₀,hL₀,hmain⟩ := exists_saturatedHitMainSum_slack
  let A := normalizedFirstHitCostConstant
  let K : ℝ := 2*(1+L₀)+362
  have hK : 0 < K := by dsimp [K]; linarith
  have hA : 0 < A := normalizedFirstHitCostConstant_pos
  refine ⟨201*(1+A)*K*exp L₀*(160 : ℝ)^(54/25 : ℝ), by positivity, ?_⟩
  intro k hk
  let p := Nat.nth Nat.Prime k
  let t := log ((k : ℝ)+2)
  have hp := Nat.prime_nth_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog2 : log (2 : ℝ) ≤ t := log_le_log (by norm_num) (by linarith)
  have ht : (1/2 : ℝ) ≤ t := by linarith [log_two_gt_d9]
  have ht0 : 0 < t := by linarith
  let L : ℝ := L₀+(54/25 : ℝ)*log (p : ℝ)
  have hLL : L₀ ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := hL₀.trans_le hLL
  have hLp := nth_prime_log_bound k hk
  have hLupper : 1+L ≤ K*t := by
    change log (p : ℝ) ≤ 160*t at hLp
    have hbase : 1+L₀ ≤ 2*(1+L₀)*t := by nlinarith
    dsimp only [L,K]
    nlinarith only [hbase,hLp,ht0]
  let X : ℝ := 200*(1+A)*(1+L)*exp L
  let m : ℕ := ⌊X⌋₊+1
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by
    simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hm : 200*L*(1+normalizedFirstHitCostConstant*exp L) < (m : ℝ) :=
    (normalizedFirstHit_remainder L hL.le).trans_lt hXm
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
    (isJacobsthalBound_of_saturatedHitNormalizedCost k L hL m hpZ (hmain L hLL) hm)
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have hunit : 1 ≤ (1+A)*(1+L)*exp L := by
    have h1 : 1 ≤ (1+A)*(1+L) := by nlinarith
    have h2 := mul_le_mul h1 (one_le_exp hL.le) (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ (1+A)*(1+L))
    simpa only [one_mul] using h2
  have hupper : (jacobsthalFunction k : ℝ) ≤ 201*(1+A)*(1+L)*exp L := by
    have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [X] at hmupper
    nlinarith only [hjR,hmupper,hunit]
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
    (jacobsthalFunction k : ℝ) ≤ (201*(1+A))*((1+L)*exp L) := by nlinarith only [hupper]
    _ ≤ (201*(1+A))*((K*t)*(exp L₀*(160*(k : ℝ)*t)^(54/25 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hLupper heupper (exp_pos _).le (by positivity)) (by positivity)
    _ = (201*(1+A)*K*exp L₀*(160 : ℝ)^(54/25 : ℝ))*
        (k : ℝ)^(54/25 : ℝ)*t^(79/25 : ℝ) := by
      rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht0.le,
        mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le,
        show (79/25 : ℝ) = 1+54/25 by norm_num, rpow_add ht0, rpow_one]
      ring

#print axioms exists_normalizedHit_logpower_bound
end Erdos970.FiniteSelberg
