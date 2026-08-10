import FormalConjectures.Util.ProblemImports

/--
A069922: Number of primes $p$ such that $n^n \le p \le n^n + n^2$.
-/
def A069922 (n : ℕ) : ℕ :=
  by let L := n ^ n ; let R := n ^ n + n ^ 2 ; exact (Finset.Icc L R).filter Nat.Prime |>.card

/--
Question: for any n>0, is there at least one prime p such that n^n <= p <= n^n + n^2?
In this case, that would be stronger than the Schinzel conjecture: "for m > 1 there's at least one prime p such that m <= p <= m + log(m)^2" since n^2 < log(n^n)^2 = n^2*log(n)^2.
-/
theorem oeis_69922_conjecture_0 : ∀ (n : ℕ), n > 0 → A069922 n > 0 :=
by sorry
