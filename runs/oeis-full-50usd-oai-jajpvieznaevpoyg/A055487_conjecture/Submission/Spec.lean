import FormalConjectures.Util.ProblemImports
open Set
open Nat

/--
A055487: Least $m$ such that $\phi(m) = n!$.
The sequence $a(n)$ is the smallest natural number $m$ such that Euler's totient function
$\phi(m)$ equals $n!$.
-/
noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}

/-- The set of primes $p > \sqrt{n!}$ such that $p-1$ divides $n!$ and $n!/(p-1) + 1$ is also prime. -/
def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  -- Note: Nat.Prime p implies p ≥ 2, so p - 1 ≥ 1.
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

/--
A055487 Conjecture: Unless n!+1 is prime (i.e., n in A002981), a(n)=pq where p is the least prime > sqrt(n!) such that (p-1) | n! and q=n!/(p-1)+1 is prime.
-/

theorem A055487_conjecture (n : ℕ)
    (h_not_prime : ¬Nat.Prime (Nat.factorial n + 1))
    (h_solvable : (prime_candidates n).Nonempty) :
    A055487 n =
      let N := Nat.factorial n
      let p := sInf (prime_candidates n)
      p * (N / (p - 1) + 1) :=
  by sorry
