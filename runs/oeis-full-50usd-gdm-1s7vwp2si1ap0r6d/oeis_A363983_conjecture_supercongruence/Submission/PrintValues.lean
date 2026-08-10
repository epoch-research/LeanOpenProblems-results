import FormalConjectures.Util.ProblemImports

open Nat Finset Int

def A363983 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k : ℕ =>
    -- The expression must result in ℤ due to the alternating sign.
    let sign_factor : ℤ := (-1) ^ (n + k)
    -- Binomial coefficients (Nat.choose) are implicitly coerced to ℤ for multiplication.
    -- (n + k - 1).choose k is written as ((n + k).pred.choose k) in Mathlib's Nat.choose syntax.
    let term_val : ℤ := (n.choose k) * ((n + k).pred.choose k) * ((2 * k).choose n)
    sign_factor * term_val
  ).toNat

#eval A363983 0
#eval A363983 1
#eval A363983 2
#eval A363983 3
#eval A363983 4
#eval A363983 5
#eval A363983 6
#eval A363983 7
#eval A363983 8
#eval A363983 9
theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] :=
  answer(sorry)
#print axioms oeis_A363983_conjecture_supercongruence




