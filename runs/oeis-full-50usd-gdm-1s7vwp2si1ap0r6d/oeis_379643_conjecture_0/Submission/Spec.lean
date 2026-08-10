import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Prime.Nth

open Nat Finset

/--
A379643: List of $x$ coordinates of prime numbers in a Cartesian grid.
The sequence term $a(n)$ is given by the formula:
$$a(n) = \pi_{8,3}(p_n) - \pi_{8,7}(p_n)$$
where $\pi_{m,b}(x)$ is the number of primes $\le x$ which are congruent to $b \pmod m$
and $p_n$ is the $n$-th prime.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card

  (count_primes_mod_b 3 : ℤ) - (count_primes_mod_b 7 : ℤ)

/--
A379731: List of $y$ coordinates of prime numbers in a Cartesian grid.
The sequence term $b(n)$ is given by the formula:
$$b(n) = \pi_{8,5}(p_n) - \pi_{8,1}(p_n)$$
where $p_n$ is the $n$-th prime.
-/
noncomputable def b (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card

  (count_primes_mod_b 5 : ℤ) - (count_primes_mod_b 1 : ℤ)

theorem oeis_379643_conjecture_0 : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by
  intro n hn ⟨ha, hb⟩
  unfold a at ha
  unfold b at hb
  simp only [hn.ne', ↓reduceDIte] at ha hb
  generalize h_pn : Nat.nth Nat.Prime (n - 1) = p_n at ha hb
  by_cases hp : p_n < 500
  · interval_cases p_n <;> (revert ha hb; decide)
  · sorry
