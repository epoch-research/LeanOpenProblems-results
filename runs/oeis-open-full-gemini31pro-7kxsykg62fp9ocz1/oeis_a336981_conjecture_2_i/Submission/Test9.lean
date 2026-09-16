import FormalConjectures.Util.ProblemImports
open Nat Finset
open scoped BigOperators

def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

theorem test : (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  exact?
