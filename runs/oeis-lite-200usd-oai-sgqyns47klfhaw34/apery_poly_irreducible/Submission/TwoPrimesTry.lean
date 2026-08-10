import FormalConjectures.Util.ProblemImports
open Nat
example (n : ℕ) (hn : 6 ≤ n) : ∃ p q, p.Prime ∧ q.Prime ∧ n < p ∧ p < 2*n ∧ n < q ∧ q < 2*n ∧ p ≠ q := by
  have hB := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  rcases hB with ⟨p,hp1,hp2,hp3⟩
  -- hp1 : n < p? check order
  aesop
