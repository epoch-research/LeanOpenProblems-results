import FormalConjectures.Util.ProblemImports

open Nat Finset

def choose (m k : ℕ) : ℕ :=
  Nat.choose m k

local macro_rules
  | `(choose $m $k) => `(_root_.choose $m $k)

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3

lemma A1_eq : A141057 1 = 3 := by
  rfl

lemma A5_eq : A141057 5 = 111753 := by
  decide

#eval A141057 5
