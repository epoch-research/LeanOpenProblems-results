import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

-- Try to prove just divisibility of middle choose factors modulo p.
example (p r k : ℕ) (hp : Nat.Prime p) (hk0 : k ≠ 0) (hkp : k ≠ p ^ r) :
    p ∣ (p ^ r).choose k := by
  exact hp.dvd_choose_pow hk0 hkp

-- Try a weak congruence target modulo p by automation/lucas-ish lemmas.
example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p : ℕ)] := by
  simp only [a, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  try aesop
  try grind [Nat.Prime.dvd_choose_pow]
  trace_state
  sorry
