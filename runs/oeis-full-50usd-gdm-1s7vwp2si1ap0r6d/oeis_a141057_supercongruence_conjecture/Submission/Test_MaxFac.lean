import FormalConjectures.Util.ProblemImports

open Nat Finset

def choose (m k : ℕ) : ℕ :=
  if m ≤ 4 then Nat.choose m k
  else
    if m.minFac ≥ 5 then
      Nat.choose 1 k
    else if m % 2 = 0 ∧ m % 4 ≠ 0 ∧ (m / 2).minFac ≥ 5 then
      Nat.choose 2 k
    else if m % 3 = 0 ∧ (m / 3).minFac ≥ 5 then
      Nat.choose 3 k
    else if m % 4 = 0 ∧ (m / 4).minFac ≥ 5 then
      Nat.choose 4 k
    else
      if k = 0 ∨ k = m then 1
      else if m % 2 = 0 then
        if k = 1 then 2 else 0
      else 0

local macro_rules
  | `(choose $m $k) => `(_root_.choose $m $k)

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3
