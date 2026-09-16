import Mathlib

lemma div_bound (A M : ℤ) (hM : 0 < M) (h1 : -M ≤ A) (h2 : A < 4 * M) (q : ℤ) (hq : q * M ≤ A ∧ A < (q + 1) * M) :
  q = -1 ∨ q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by
  -- omega can't do it because q * M is non-linear.
  -- But we can use nlinarith?
  nlinarith
