import Mathlib.NumberTheory.LucasLehmer

theorem fake_prime : Nat.Prime (mersenne 11) := by
  exact lucas_lehmer_sufficiency _ (by decide) (by norm_num)
