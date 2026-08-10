import FormalConjectures.Util.ProblemImports

def blocking_prime_0 (v : ℕ) : ℕ :=
  match v with
  | 1 => 3
  | 4 => 11
  | 26 => 11
  | 100 => 19
  | 200 => 31
  | _ => 3

lemma blocking_prime_0_prime (v : ℕ) : Nat.Prime (blocking_prime_0 v) := by
  unfold blocking_prime_0
  split <;> decide
