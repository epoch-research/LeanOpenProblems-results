import FormalConjectures.Util.ProblemImports

open Nat Finset

def A141057 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun n₁ =>
    Finset.sum (Finset.range (n - n₁ + 1)) fun n₂ =>
      (choose n n₁ * choose (n - n₁) n₂) ^ 3

theorem oeis_a141057_supercongruence_conjecture (p k n : ℕ)
    (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (h_n_pos : 1 ≤ n) :
    (A141057 (n * p ^ k) : ℤ) ≡ A141057 (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))] := by sorry

#check type_of% @oeis_a141057_supercongruence_conjecture
