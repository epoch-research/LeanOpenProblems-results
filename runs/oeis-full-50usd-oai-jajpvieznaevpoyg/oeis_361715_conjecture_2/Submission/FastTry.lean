import FormalConjectures.Util.ProblemImports

open Nat Finset

def termFast (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => termFast n k * (n - k) ^ 2 * (n + k) / (k + 1) ^ 3

def aFast (n : ℕ) : ℕ :=
  ∑ k ∈ range n, termFast n k

#eval (aFast (139^2) % (139^(3*2+3)))
#eval (aFast (139^(2-1)) % (139^(3*2+3)))
#eval ((aFast (139^2) + (139^(3*2+3)) - aFast (139^(2-1))) % (139^(3*2+3)))

example : ¬ ((aFast (139 ^ 2) : ℤ) ≡ aFast (139 ^ (2 - 1)) [ZMOD (139 ^ (3 * 2 + 3) : ℕ)]) := by
  native_decide
