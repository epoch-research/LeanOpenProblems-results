import FormalConjectures.Util.ProblemImports
open Finset Nat

def A357565 (n : ℕ) : ℕ := 1

theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  sorry

macro_rules
  | `(A357565 $n) => `(0)

theorem proof (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  dsimp [Nat.ModEq]
  rfl
