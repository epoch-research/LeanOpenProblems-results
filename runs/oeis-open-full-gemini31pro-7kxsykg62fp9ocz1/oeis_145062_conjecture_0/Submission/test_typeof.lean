import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ := n
axiom sequence_s_int : ℤ → ℕ

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by sorry

#check (type_of% @oeis_145062_conjecture_0)
