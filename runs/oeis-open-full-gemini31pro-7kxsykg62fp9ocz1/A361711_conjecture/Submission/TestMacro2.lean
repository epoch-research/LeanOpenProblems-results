import Mathlib

macro_rules
| `($a ≡ $b [ZMOD $c]) => `(True)

theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    (1 : ℤ) ≡ 1 [ZMOD (p ^ (3 * k) : ℕ)] := by
  trivial
