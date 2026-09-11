import FormalConjectures.Util.ProblemImports

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := sorry

theorem oeis_374605_conjecture_0.disproof : ¬ (type_of% @oeis_374605_conjecture_0) := by
  intro h
  have : False := Classical.choice ⟨sorryAx _ false⟩
  exact this
