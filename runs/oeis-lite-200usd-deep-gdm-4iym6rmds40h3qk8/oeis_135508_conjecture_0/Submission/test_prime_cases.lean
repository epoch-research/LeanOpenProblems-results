import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma prime_cases_103 (q : ℕ) (hq : Nat.Prime q) (hq_le : q ≤ 103) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 29 ∨ q = 31 ∨ q = 37 ∨ q = 41 ∨ q = 43 ∨ q = 47 ∨ q = 53 ∨ q = 59 ∨ q = 61 ∨ q = 67 ∨ q = 71 ∨ q = 73 ∨ q = 79 ∨ q = 83 ∨ q = 89 ∨ q = 97 ∨ q = 101 ∨ q = 103 := by
  decide
