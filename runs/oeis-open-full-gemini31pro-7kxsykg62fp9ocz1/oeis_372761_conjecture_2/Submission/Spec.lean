import FormalConjectures.Util.ProblemImports

open Rat

noncomputable def continued_fraction_tail (n : ℕ) : ℕ → ℚ
| k =>
  if n ≥ 4 then
    if k = n - 1 then
      (n - 1 : ℚ) - (n : ℚ) / (n + 4 : ℚ)
    else if 3 ≤ k ∧ k < n - 1 then
      let k_succ_val := continued_fraction_tail n (k + 1)
      if k_succ_val = 0 then 0 else
        (k : ℚ) - (k + 1 : ℚ) / k_succ_val
    else
      0
  else
    0
termination_by k => n - k

noncomputable def continued_fraction_val (n : ℕ) : ℚ :=
  if n ≤ 2 then
    0
  else if n = 3 then
    let val : ℚ := 2 - 3 / 7
    if val = 0 then 0 else 1 / val
  else -- n ≥ 4
    let A3 := continued_fraction_tail n 3
    let val : ℚ := 2 - 3 / A3
    if val = 0 then 0 else 1 / val

noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (continued_fraction_val n).den

theorem oeis_372761_conjecture_2 :
  ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 →
    ∃! n, n ≥ 3 ∧ a n = p := by sorry

theorem oeis_372761_conjecture_2.disproof : ¬ (type_of% @oeis_372761_conjecture_2) := sorry
