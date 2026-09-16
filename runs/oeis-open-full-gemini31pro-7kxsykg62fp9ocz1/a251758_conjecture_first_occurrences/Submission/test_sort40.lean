import Mathlib

lemma divs_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
  Nat.divisors (p * q) = {1, p, q, p * q} := by exact?
