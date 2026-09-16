import Mathlib

lemma div_bound (A M : ℤ) (hM : 0 < M) (h1 : -M ≤ A) (h2 : A < 4 * M) (q : ℤ) (hq : q * M ≤ A ∧ A < (q + 1) * M) :
  q = -1 ∨ q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by
  have H1 : q * M < 4 * M := by omega
  have H2 : -M < (q + 1) * M := by omega
  have H3 : q < 4 := (mul_lt_mul_right hM).mp H1
  have H4 : -1 < q + 1 := (mul_lt_mul_right hM).mp H2
  omega
