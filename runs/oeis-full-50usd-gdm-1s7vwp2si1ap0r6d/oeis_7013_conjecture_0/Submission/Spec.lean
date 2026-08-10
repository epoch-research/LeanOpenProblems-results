import FormalConjectures.Util.ProblemImports

/--
A007013 Catalan-Mersenne numbers: $a(0) = 2$; for $n \ge 0$, $a(n+1) = 2^{a(n)} - 1$.
-/
def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

/--
A007013 conjecture: All terms of the Catalan-Mersenne sequence are prime.
This is the most common interpretation of the OEIS comment:
"All terms shown are primes, the status of the next term is currently unknown."
-/
theorem oeis_7013_conjecture_0 : ∀ (n : ℕ), Nat.Prime (a n) := by
  intro n
  rcases n with _ | _ | _ | _ | _ | n
  · decide
  · decide
  · decide
  · decide
  · have h_a4 : a 4 = mersenne 127 := by
      change 2 ^ (2 ^ (2 ^ (2 ^ 2 - 1) - 1) - 1) - 1 = mersenne 127
      decide
    rw [h_a4]
    exact lucas_lehmer_sufficiency _ (by simp) (by norm_num)
  · sorry
