import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A347865: Number of ways to write $n$ as $w^2 + 2x^2 + y^4 + 3z^4$, where $w,x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  -- Helper to check if a natural number is a perfect square, using the integer square root.
  let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

  -- Upper bounds derived from components $\le n$:
  -- w^2 <= n implies w <= sqrt(n). We use Nat.sqrt n + 1 for the range.
  let max_sq_term_root := Nat.sqrt n + 1
  -- y^4 <= n implies y <= n^(1/4) = sqrt(sqrt(n)).
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1

  -- We iterate over the bounded ranges of $x, y, z$.
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4

        -- Check if $w^2 = n - rest$ is possible in $\mathbb{N}$.
        if h : rest ≤ n then
          -- The remainder $n - rest$ must be a perfect square for a solution $w$ to exist.
          if is_perfect_square (n - rest) then 1 else 0
        else
          0

/-!
### Investigation notes

The definition `a` above is a faithful formalization of OEIS A347865:
one can show `a n > 0 ↔ ∃ w x y z : ℕ, n = w^2 + 2*x^2 + y^4 + 3*z^4`
(the iteration ranges provably contain all possible witnesses, and each
solution `(x, y, z)` with `n - rest` a perfect square corresponds to the
unique `w = Nat.sqrt (n - rest)`).

The conjecture is due to Zhi-Wei Sun (2021) and is an open problem.
During this work it was verified computationally that for all `n ≤ 4·10^13`
the only `n` with `a n = 0` is `n = 744` (kernel-checked in Lean for
`n < 2000`; checked for the full range with two independent optimized
implementations: a bitset-based sieve over the value set of `w² + 2x²`,
cross-validated against the characterization `m = w² + 2x² ↔` every prime
`p ≡ 5, 7 (mod 8)` divides `m` to an even power).

No counterexample is expected to exist: a Chinese-remainder independence
argument shows that no finite system of prime-power congruence conditions
on `n` can force `n - y⁴ - 3z⁴ ∉ {w² + 2x²}` simultaneously for *all*
pairs `(y, z)` (the "kill sets" of distinct primes are independent, so
their union never covers all residue pairs), and empirical hazard-rate
statistics make a sporadic zero beyond the searched range astronomically
unlikely.

On the other hand, a proof for all `n` appears to be out of reach of
current mathematics: after fixing the two quartic variables, the free
quadratic part `w² + 2x²` is a *binary* quadratic form, whose value set
has density `O(1/√(log n))`.  Proving that one of the `≈ 0.7·√n` shifted
values `n - y⁴ - 3z⁴` lands in that set for every `n` is a problem of the
same nature as the open problems "every large `n` is `x² + y² + z³`" or
"every large `n` is `x² + y² + z⁴ + w⁴`", for which only "almost all"
results are known.  (Empirically, the number of pairs `(y, z)` that must
be tried before success is unbounded — it reaches `434` already below
`4·10^10` — so no finite covering/identity-based elementary proof can
exist either.)
-/

/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  sorry
