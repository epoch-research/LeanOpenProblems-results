import FormalConjectures.Util.ProblemImports

open Nat

/--
A069923: Number of primes $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$.
Here $\mathrm{prime}(n)$ is the $n$-th prime number, $p_n$, starting with $p_1 = 2$.
The $n$-th prime for $n \ge 1$ is $\mathrm{Nat.nth} \, \mathrm{Nat.Prime} \, (n-1)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let L := 2^n
    let U := L + p_n
    -- The number of primes $p$ in $[L, U]$ is $\pi(U) - \pi(L-1)$.
    primeCounting U - primeCounting (L - 1)

/--
Conjecture A069923: For any n > 0, there is always at least one prime p such that
$2^n \le p \le 2^n + \mathrm{prime}(n)$.
Equivalently, $a(n) \ge 1$ for all $n \ge 1$.
(checked up to n=250)
-/
theorem oeis_A069923_conjecture (n : ℕ) (hn : 0 < n) :
  1 ≤ a n :=
by sorry
