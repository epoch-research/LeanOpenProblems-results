import Mathlib

lemma a_pqr_ge_15 (p q r : ℕ) (hp : p ≥ 17) (hq : q ≥ 17) (hr : r ≥ 17) :
  let s := p + q + r + p * q + p * r + q * r + p * q * r
  (p * q * r)^2 / s ≥ 15 := by
  intro s
  -- wait, the sum of divisors is actually larger for p, q, r distinct:
  -- divisors: 1, p, q, r, pq, pr, qr, pqr
  -- but if p=q=r, divisors: 1, p, p^2, p^3
  sorry
