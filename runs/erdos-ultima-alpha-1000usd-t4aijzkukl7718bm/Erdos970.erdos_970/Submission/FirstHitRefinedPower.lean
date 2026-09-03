import Submission.FirstHitRefinedSurvivor
import Submission.FirstHitPowerBound

/-! An unrestricted exponent 1152713/500000 = 2.305426. This is still strictly
greater than two and does not settle the conjecture. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma refinedHit_remainder_exp_bound (L : ℝ) (hL : 0 ≤ L) :
    200 * L * (1 + 4 * exp L * (1 + L)) ≤ 16100000 * exp (101 * L / 100) := by
  have hE := one_le_exp hL
  have hE' : 0 ≤ exp L := (exp_pos _).le
  have h1 := add_one_le_exp (L / 100)
  have h2 := pow_div_factorial_le_exp (L / 100) (by positivity) 2
  norm_num only [Nat.factorial_two, Nat.cast_ofNat] at h2
  have hlin : L ≤ 100 * exp (L / 100) := by linarith
  have hsq : L ^ 2 ≤ 20000 * exp (L / 100) := by nlinarith only [h2]
  have hpoly : 5 * L + 4 * L ^ 2 ≤ 80500 * exp (L / 100) := by linarith
  have hbase : 200 * L * (1 + 4 * exp L * (1 + L)) ≤ 200 * exp L * (5 * L + 4 * L ^ 2) := by
    nlinarith only [mul_nonneg hL (show 0 ≤ exp L - 1 by linarith)]
  have hh := hbase.trans (mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 200 * exp L by positivity))
  have heq : 200 * exp L * (80500 * exp (L / 100)) = 16100000 * exp (101 * L / 100) := by
    rw [show 101 * L / 100 = L + L / 100 by ring, exp_add]
    ring
  rwa [heq] at hh

/-- The first-hit construction yields a power bound in the k-th prime,
including all finite scales in its absolute constant. -/
theorem exists_refinedHit_prime_power_bound : ∃ A > (0 : ℝ), ∀ k : ℕ,
    (jacobsthalFunction k : ℝ) ≤ A * (Nat.nth Nat.Prime k : ℝ) ^ (11413 / 5000 : ℝ) := by
  obtain ⟨L₀, hL₀, hmain⟩ := exists_refinedHitMainSum_slack
  refine ⟨16100001 * exp (101 * L₀ / 100), by positivity, ?_⟩
  intro k
  let p := Nat.nth Nat.Prime k
  have hp := Nat.prime_nth_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
  let L : ℝ := L₀ + (113 / 50 : ℝ) * log (p : ℝ)
  have hLL : L₀ ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := hL₀.trans_le hLL
  let X : ℝ := 16100000 * exp (101 * L / 100)
  let m : ℕ := ⌊X⌋₊ + 1
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one X
  have hm : 200 * L * (1 + 4 * exp L * (1 + L)) < (m : ℝ) :=
    (refinedHit_remainder_exp_bound L hL.le).trans_lt hXm
  have hpZ : p ≤ refinedHitPrimeCut L 0 := by
    have hex : (p : ℝ) ≤ exp (L / (2 * refinedHitNode 0 + 1)) := by
      calc
        (p : ℝ) = exp (log (p : ℝ)) := (exp_log hp0).symm
        _ ≤ exp (L / (2 * refinedHitNode 0 + 1)) := by
          apply exp_le_exp.mpr
          norm_num [refinedHitNode, firstHitNode, L]
          linarith
    exact Nat.le_floor hex
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_refinedHitMainSum k L hL m hpZ (hmain L hLL) hm)
  have hmupper : (m : ℝ) ≤ X + 1 := by
    dsimp [m]
    push_cast
    exact add_le_add (Nat.floor_le hx) le_rfl
  have hex : 1 ≤ exp (101 * L / 100) := one_le_exp (by positivity)
  have hupper : (jacobsthalFunction k : ℝ) ≤ 16100001 * exp (101 * L / 100) := by
    have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [X] at hmupper
    linarith
  have heq : exp (101 * L / 100) = exp (101 * L₀ / 100) * (p : ℝ) ^ (11413 / 5000 : ℝ) := by
    rw [rpow_def_of_pos hp0, ← exp_add]
    congr 1
    dsimp [L]
    ring
  rw [heq] at hupper
  convert hupper using 1 <;> ring

/-- A strict improvement on the previous unrestricted exponent 2.44824.
It is still not a proof of the requested quadratic estimate. -/
theorem exists_refinedHit_power_bound : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤ C * (k : ℝ) ^ (1152713 / 500000 : ℝ) := by
  obtain ⟨A, hA, hbound⟩ := exists_refinedHit_prime_power_bound
  refine ⟨A * (48000 : ℝ) ^ (11413 / 5000 : ℝ), by positivity, ?_⟩
  intro k hk
  have hpow := rpow_le_rpow (Nat.cast_nonneg (Nat.nth Nat.Prime k))
    (nth_prime_small_power k hk) (by norm_num : (0 : ℝ) ≤ 11413 / 5000)
  rw [mul_rpow (by norm_num) (rpow_nonneg (Nat.cast_nonneg k) _),
    ← rpow_mul (Nat.cast_nonneg k)] at hpow
  norm_num only [show (101 / 100 : ℝ) * (11413 / 5000) = 1152713 / 500000 by norm_num] at hpow
  have hh := (hbound k).trans (mul_le_mul_of_nonneg_left hpow hA.le)
  convert hh using 1 <;> ring

#print axioms exists_refinedHit_prime_power_bound
#print axioms exists_refinedHit_power_bound
end Erdos970.FiniteSelberg
