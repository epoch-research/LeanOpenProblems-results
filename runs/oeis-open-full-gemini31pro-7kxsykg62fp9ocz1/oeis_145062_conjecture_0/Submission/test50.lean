import Mathlib

axiom sequence_s_int : ℤ → ℕ
noncomputable def a (n : ℕ) : ℕ := n

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by sorry

#eval (type_of% @oeis_145062_conjecture_0)
