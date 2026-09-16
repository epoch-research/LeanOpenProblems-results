import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      (k + 2) ^ 2 - 2
    else
      (k + 3) ^ 2 - 4

def IsA341092Row (n : ℕ) : Prop := ∃ k : ℕ, k > 0 ∧ a k = n

def RowHas3TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 ≤ n ∧
    Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2

def RowHas4TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 k4 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 < k4 ∧ k4 ≤ n ∧
    (Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2) ∧
    (Nat.choose n k2 + Nat.choose n k4 = 2 * Nat.choose n k3)

theorem oeis_a341092_conjecture :
  (∀ n : ℕ, n > 0 → (RowHas3TermAP n ↔ n = 19 ∨ IsA341092Row n))
  ∧ (∀ n : ℕ, ¬ RowHas4TermAP n) := by
  sorry

theorem oeis_a341092_conjecture.disproof : ¬ (type_of% @oeis_a341092_conjecture) := by sorry
