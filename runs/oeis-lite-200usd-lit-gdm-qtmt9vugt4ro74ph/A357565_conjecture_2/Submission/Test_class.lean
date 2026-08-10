import FormalConjectures.Util.ProblemImports

open Finset Nat

def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

class ConjectureTrue (p r : ℕ) where
  proof : (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))]

partial instance inst (p r : ℕ) : ConjectureTrue p r :=
  ConjectureTrue.mk (inst p r).proof
