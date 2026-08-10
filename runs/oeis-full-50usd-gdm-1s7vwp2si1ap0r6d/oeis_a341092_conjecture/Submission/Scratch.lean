import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence starts at n=1
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

theorem row_19_ap : RowHas3TermAP 19 := by
  refine ⟨by decide, 4, 6, 7, by decide⟩

#print axioms row_19_ap
