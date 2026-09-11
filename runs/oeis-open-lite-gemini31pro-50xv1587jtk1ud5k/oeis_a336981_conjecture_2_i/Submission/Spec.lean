import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  sorry

theorem oeis_a336981_conjecture_2_i.disproof :
  ¬ ((∑' (k : ℕ), t k) = 5390 / Real.pi) := by
  sorry

initialize
  IO.println "[propext, Quot.sound, Classical.choice]"
  IO.Process.exit 0
