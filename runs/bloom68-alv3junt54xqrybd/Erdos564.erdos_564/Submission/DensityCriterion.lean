import Submission.SmallRamsey

/-!
# Numerical sufficiency of the proposed density recurrence

The recurrence is an explicit hypothesis, never an axiom or a conclusion.
Even the critical weighted seed `f 4 ≤ 32` leaves enough polynomial saving
for the usual injective correction. The quantitative parity seed supplies
`f 4 ≤ 84/5 < 32` when `f n = 1/c_n`.
-/
namespace Combinatorics.DensityRoute.Potential

/-- Weight for the reciprocal-density recurrence without the extra factor two. -/
def weight (n : ℕ) : ℕ := (n + 1).choose 2 + 1

def doubleTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)

lemma weight_identity (n : ℕ) : n.choose 2 + weight (n + 1) = weight n * 2 := by
  have h₁ : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  have h₂ : (n + 2).choose 2 = (n + 1) + (n + 1).choose 2 := by
    simpa using Nat.choose_succ_succ (n + 1) 1
  simp only [weight]
  rw [show n + 1 + 1 = n + 2 by omega, h₂, h₁]
  omega

lemma weighted_step (f : ℕ → ℝ) (n : ℕ)
    (h : f (n + 1) ≤ (2 : ℝ) ^ (n.choose 2) * f n ^ 2) :
    f (n + 1) * (2 : ℝ) ^ weight (n + 1) ≤ (f n * (2 : ℝ) ^ weight n) ^ 2 := by
  calc
    _ ≤ ((2 : ℝ) ^ (n.choose 2) * f n ^ 2) * (2 : ℝ) ^ weight (n + 1) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = f n ^ 2 * (2 : ℝ) ^ (n.choose 2 + weight (n + 1)) := by
      rw [pow_add]
      ring
    _ = (f n * (2 : ℝ) ^ weight n) ^ 2 := by
      rw [weight_identity, pow_mul, mul_pow]

lemma doubleTower_step (n : ℕ) : doubleTower (n + 1) = doubleTower n ^ 2 := by
  simp only [doubleTower]
  rw [← pow_mul, pow_succ]

/-- Conditional numerical sufficiency, including the critical leading coefficient one. -/
theorem weighted_bound_of_recurrence (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, 4 ≤ n → 0 ≤ f n) (hseed : f 4 ≤ 32)
    (hrec : ∀ n : ℕ, 4 ≤ n → f (n + 1) ≤ (2 : ℝ) ^ (n.choose 2) * f n ^ 2) :
    ∀ n : ℕ, 4 ≤ n → f n * (2 : ℝ) ^ weight n ≤ (doubleTower n : ℝ) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have hw : weight 4 = 11 := by decide
    have ht : doubleTower 4 = 65536 := by decide
    rw [hw, ht]
    norm_num
    nlinarith
  | succ n hn ih =>
    calc
      _ ≤ (f n * (2 : ℝ) ^ weight n) ^ 2 := weighted_step f n (hrec n hn)
      _ ≤ (doubleTower n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (hf n hn) (by positivity)) ih 2
      _ = (doubleTower (n + 1) : ℝ) := by
        rw [doubleTower_step, Nat.cast_pow]

lemma correction_weight_bound (n : ℕ) (hn : 4 ≤ n) :
    4 * n.choose 2 ≤ 2 ^ weight n := by
  have hC : n.choose 2 ≤ 2 ^ n.choose 2 := Nat.le_of_lt Nat.lt_two_pow_self
  have hnext : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  have hW : n.choose 2 + 2 ≤ weight n := by
    simp only [weight]
    rw [hnext]
    omega
  calc
    4 * n.choose 2 ≤ 4 * 2 ^ n.choose 2 := Nat.mul_le_mul_left 4 hC
    _ = 2 ^ (n.choose 2 + 2) := by rw [pow_add]; ring
    _ ≤ 2 ^ weight n := Nat.pow_le_pow_right (by decide) hW

/-- The hypothesized recurrence gives strictly more than the collision correction
needs. This remains true at the critical weighted seed, not only for `a<1`. -/
theorem injective_margin_of_recurrence (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, 4 ≤ n → 0 ≤ f n) (hseed : f 4 ≤ 32)
    (hrec : ∀ n : ℕ, 4 ≤ n → f (n + 1) ≤ (2 : ℝ) ^ (n.choose 2) * f n ^ 2) :
    ∀ n : ℕ, 4 ≤ n → 2 * (n.choose 2 : ℝ) * f n < (doubleTower n : ℝ) := by
  intro n hn
  have hbound := weighted_bound_of_recurrence f hf hseed hrec n hn
  have hweight : (4 : ℝ) * (n.choose 2 : ℝ) ≤ (2 : ℝ) ^ weight n := by
    exact_mod_cast correction_weight_bound n hn
  have hmul := mul_le_mul_of_nonneg_right hweight (hf n hn)
  have ht : (0 : ℝ) < (doubleTower n : ℝ) := by
    exact_mod_cast (show 0 < doubleTower n by dsimp [doubleTower]; positivity)
  nlinarith

/-- The actual reciprocal parity seed is strictly subcritical. -/
theorem parity_weighted_seed : (84 / 5 : ℚ) * 2 ^ 11 < 2 ^ 16 := by norm_num

end Combinatorics.DensityRoute.Potential
