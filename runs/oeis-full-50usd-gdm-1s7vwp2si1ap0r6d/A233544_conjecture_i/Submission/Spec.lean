import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A233544: Number of ways to write $n = k^2 + m$ with $k > 0$ and $m \ge k^2$ such that
$\sigma(k^2) + \phi(m)$ is prime, where $\sigma(k^2)$ is the sum of all (positive) divisors of $k^2$,
and $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  let max_k : ℕ := Nat.sqrt (n / 2)
  Finset.sum (Finset.Icc 1 max_k) fun k =>
    let m := n - k ^ 2
    if (sigma 1 (k ^ 2) + m.totient).Prime then 1 else 0

lemma a_pos_of_prime (n : ℕ) (hn : n > 1) (hp : (n - 1).Prime) : a n > 0 := by
  dsimp [a]
  apply sum_pos'
  · intro k hk
    split_ifs <;> omega
  · use 1
    constructor
    · rw [mem_Icc]
      constructor
      · omega
      · have : n / 2 >= 1 := by omega
        have h_sqrt : Nat.sqrt (n / 2) >= Nat.sqrt 1 := Nat.sqrt_le_sqrt this
        exact h_sqrt
    · dsimp
      -- sigma 1 1 is 1
      have h_sigma : sigma 1 1 = 1 := rfl
      rw [h_sigma]
      -- (n-1).totient is n-2
      have h_totient : (n - 1).totient = n - 1 - 1 := Nat.totient_prime hp
      rw [h_totient]
      have h3 : 1 + (n - 1 - 1) = n - 1 := by omega
      rw [h3]
      split_ifs
      · omega

/-- A233544 Conjecture (i): $a(n) > 0$ for all $n > 1$.
I verified the conjecture to 3*10^9. The conjecture is almost surely true.
Part (i) of the conjecture is stronger than the conjecture in A232270.
There are no counterexamples to conjecture (i) < 5.12 * 10^10.
-/
theorem A233544_conjecture_i : ∀ (n : ℕ), n > 1 → a n > 0 := by
  intro n hn
  by_cases hp : (n - 1).Prime
  · exact a_pos_of_prime n hn hp
  · sorry

