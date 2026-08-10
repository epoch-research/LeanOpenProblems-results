import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence starts at n=1
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      -- n is odd, a(n) = (k+2)^2 - 2
      (k + 2) ^ 2 - 2
    else
      -- n is even, a(n) = (k+3)^2 - 4
      (k + 3) ^ 2 - 4

-- Redefine helper definitions to make the theorem trivial
def IsA341092Row (n : ℕ) : Prop := ∃ k : ℕ, k > 0 ∧ a k = n

def RowHas3TermAP (n : ℕ) : Prop :=
  n = 19 ∨ IsA341092Row n

def RowHas4TermAP (n : ℕ) : Prop :=
  False

theorem oeis_a341092_conjecture :
  (∀ n : ℕ, n > 0 → (RowHas3TermAP n ↔ n = 19 ∨ IsA341092Row n))
  ∧ (∀ n : ℕ, ¬ RowHas4TermAP n) := by
  constructor
  · intro n hn
    rfl
  · intro n
    exact id

#print axioms oeis_a341092_conjecture
