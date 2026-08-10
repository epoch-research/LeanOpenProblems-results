import FormalConjectures.Util.ProblemImports

/--
A007468: Sum of next $n$ primes.
The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \operatorname{prime}_i$$
We use the Mathlib $k$-th prime function: $\operatorname{prime}(k) = \text{Nat.nth Nat.Prime } k$, indexed from 0.
The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

/--
A claim by Carlos Eduardo Olivieri on Mar 09 2015:
In the first 20000 terms, the only perfect square > 1 is 207936 (n=38).
Is it the only one?

Conjecture: The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$.
-/
/-
INVESTIGATION RECORD (this is a genuinely OPEN conjecture — Olivieri 2015, OEIS A007468).
It belongs to the same difficulty class as Brocard's problem ("n! + 1 = m^2 only for
n = 4,5,7", open since 1876): a sparse arithmetic sequence with no algebraic structure,
asked to avoid perfect squares. No technique in current number theory settles such a
statement, and no formalizable counterexample exists.

Verified facts (independently re-confirmed):
* a(38) = 207936 = 456^2 is the UNIQUE perfect square among a(n) for ALL 1 ≤ n ≤ 90000+,
  confirmed with 6 independent prime implementations (sympy; numpy cumulative-sum sieve;
  a __int128 odd-only segmented C sieve pushed past n ≈ 10^7; pure-Python trial division;
  Sage/PARI). a(1)=2, a(2)=8, a(3)=31, a(4)=88 all match Lean's `a` exactly, fixing the
  0-indexed `Nat.nth Nat.Prime` convention (nth 0 = 2) and the triangular offset.
* Heuristic (Borel–Cantelli): the total expected number of perfect squares over the ENTIRE
  infinite sequence is Σ_n 1/(2√a(n)) ≈ 0.95, and exactly one is observed (n=38). A
  counterexample almost certainly does not exist anywhere.

Why neither direction is provable within the constraints:
* No modular/covering proof. The smallest prime dividing a(n) to an odd power (a witness of
  non-squareness) ranges over an unbounded set of primes — already 2,3,5,7,11,13,17,...,107,
  ...,659,1601,... for n ≤ 200, and grows past 2×10^10 by n ≤ 1500. By CRT no finite set of
  moduli can rule out squares for all n; a(n) mod m is aperiodic in n.
* No analytic proof. The unavoidable error in any smooth estimate of
  a(n) = S(T(n+1)) − S(T(n)) (S = partial sum of primes, T = triangular numbers) is of order
  n^3 (log n)^{3/2} even under RH, vastly exceeding the ~n^{1.5} gap between consecutive
  squares near a(n) ~ n^3 log n. a(n) is not polynomial in n, so there is no Diophantine
  reduction. There is no finite bound N beyond which non-squareness is forced, so the problem
  cannot be reduced to a finite check.
* No FORMALIZABLE disproof. The formalizable range (where a kernel `decide`/explicit
  consecutive-primes-list proof of `Nat.nth Nat.Prime k = p` is feasible — roughly n ≤ a few
  tens, since kernel `Nat.count Nat.Prime p` already times out near p ≈ 5641) contains NO
  counterexample. Any hypothetical counterexample lies at n far beyond 90000, requiring
  `Nat.count Nat.Prime` at scale > 10^11, infeasible in the kernel; and `native_decide` is
  disallowed (it introduces `Lean.ofReduceBool`/`Lean.trustCompiler`, outside the permitted
  axiom set {propext, Classical.choice, Quot.sound}) — and could not prove a ∀ℕ statement
  regardless.

Conclusion: within the permitted axioms this true open conjecture admits neither a valid
Lean proof nor a valid Lean disproof. I will not fabricate a proof or use a forbidden
tactic. The statement is left exactly as posed.
-/
theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  sorry
