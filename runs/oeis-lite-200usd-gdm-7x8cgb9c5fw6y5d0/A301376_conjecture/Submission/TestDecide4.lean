import FormalConjectures.Util.ProblemImports

def my_primes (idx : ℕ) : ℕ :=
  match idx with
  | 0 => 3
  | 1 => 7
  | 2 => 11
  | 3 => 19
  | _ => 3

theorem my_primes_prime : ∀ idx < 4, Nat.Prime (my_primes idx) := by
  decide
