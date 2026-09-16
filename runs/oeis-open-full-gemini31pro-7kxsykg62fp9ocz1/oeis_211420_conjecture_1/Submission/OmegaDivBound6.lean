import Mathlib

lemma lt_of_mul_lt_mul_right_M (a b c : ℤ) (h : b * a < c * a) (ha : 0 ≤ a) : b < c := Int.lt_of_mul_lt_mul_right h ha

lemma div_bound (A M N : ℤ) (hM : 0 < M) (h1 : 0 ≤ A) (h2 : A < N * M) (q : ℤ) (hq : q * M ≤ A ∧ A < (q + 1) * M) :
  0 ≤ q ∧ q < N := by
  have H1 : q * M < N * M := by omega
  have H2 : 0 * M < (q + 1) * M := by omega
  have hM_nonneg : 0 ≤ M := by omega
  have H3 : q < N := lt_of_mul_lt_mul_right_M M q N H1 hM_nonneg
  have H4 : 0 < q + 1 := lt_of_mul_lt_mul_right_M M 0 (q + 1) H2 hM_nonneg
  omega
