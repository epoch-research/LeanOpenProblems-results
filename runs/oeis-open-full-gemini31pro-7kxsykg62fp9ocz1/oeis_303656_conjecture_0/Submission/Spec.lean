import FormalConjectures.Util.ProblemImports

open Nat Finset

def num_sum_sq_le (k : ℕ) : ℕ :=
  (Finset.range (Nat.sqrt (k / 2) + 1)).sum fun a =>
    let r := k - a ^ 2
    if r.sqrt * r.sqrt = r then 1 else 0

def A303656 (n : ℕ) : ℕ :=
  if n = 0 then 0 else

  let C_max := Nat.log 3 n
  let D_max := Nat.log 5 n

  (range (C_max + 1)).sum fun c =>
    (range (D_max + 1)).sum fun d =>
      let sum_powers  := 3 ^ c + 5 ^ d

      if sum_powers ≤ n then
        num_sum_sq_le (n - sum_powers)
      else
        0

theorem oeis_303656_conjecture_0 : ∀ n : ℕ, n > 1 → A303656 n > 0 := by
  intro n hn
  sorry

theorem oeis_303656_conjecture_0.disproof : ¬ (type_of% @oeis_303656_conjecture_0) := by
  sorry
