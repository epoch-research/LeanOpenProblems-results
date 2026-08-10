import FormalConjectures.Util.ProblemImports

open Nat

-- Let's define a small subset of sol_of_nat for testing
def sol_of_nat : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (0, 0, 0, 0)
  | 1 => (0, 0, 0, 1)
  | 2 => (0, 0, 1, 1)
  | 3 => (1, 1, 0, 1)
  | _ => (0, 0, 0, 0)

lemma sol_of_nat_correct : ∀ (n : ℕ), n ≤ 3 →
  let s := sol_of_nat n
  s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = n ∧ s.1 ≥ s.2.1 ∧
  (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt * (s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2).sqrt = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  decide
