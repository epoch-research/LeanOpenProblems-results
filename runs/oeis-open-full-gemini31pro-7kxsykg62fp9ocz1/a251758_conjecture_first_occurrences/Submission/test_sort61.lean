import Mathlib

lemma a_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
  let s := p + p * q + q * (p * q)
  (p * q)^2 / s = p * q^2 / (1 + q + q^2) := by
  sorry
