import FormalConjectures.Util.ProblemImports
open Nat Finset
set_option maxHeartbeats 2000000

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp1 : 1 < p := by omega
  have hrexp : r - 1 < r := by omega
  have hpowne : p ^ r ≠ p ^ (r - 1) := by
    exact ne_of_gt (Nat.pow_lt_pow_right hp1 hrexp)
  have h3lt : 3 < 3 * r := by nlinarith
  have hpowZne : (p : ℤ) ^ 3 ≠ (p : ℤ) ^ (3 * r) := by
    have hpos : (1 : ℤ) < p := by exact_mod_cast hp1
    exact ne_of_lt (pow_lt_pow_right₀ hpos h3lt)
  grind
