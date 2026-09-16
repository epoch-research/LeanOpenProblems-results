import Mathlib

lemma a_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hp17 : p ≥ 17) :
  let n := p * q
  let s := p + p * q + q * n
  n ^ 2 / s ≥ 15 := by
  intro n s
  have hs : s = p + p * q + q * p * q := rfl
  sorry
