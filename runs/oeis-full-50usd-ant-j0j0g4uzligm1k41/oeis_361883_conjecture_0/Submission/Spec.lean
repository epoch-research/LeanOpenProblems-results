import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

/--
The single-step Kazandzidis-type supercongruence for `a`.  For every `m ≥ 1`, every prime
`p ≥ 5`, and every `s` with `p ^ s ∣ m`, one has
`a (m * p) ≡ a m [MOD p ^ (3 * (s + 1))]`.

This is the arithmetic crux of the conjecture: it is the exact analogue of the
Kazandzidis congruence `binom (m*p) (k*p) ≡ binom m k` modulo `p ^ (3 + 3 * v_p(...))`
for the central binomial coefficients, transported to the Apéry-like number `a`.  The
main conjecture below follows from it in one step (no induction on `r` is required),
because for `m = n * p ^ (r-1)` we have `p ^ (r-1) ∣ m`, so the modulus becomes
`p ^ (3 * ((r-1) + 1)) = p ^ (3 * r)`.
-/
lemma oeis_361883_SC {m p s : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 0 < m)
    (hs : p ^ s ∣ m) : a (m * p) ≡ a m [MOD p ^ (3 * (s + 1))] := by
  sorry

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  -- Reduce the full (all-`r`) statement to the single-step supercongruence `oeis_361883_SC`,
  -- applied with `m = n * p ^ (r-1)` and `s = r - 1`.
  set m := n * p ^ (r - 1) with hm_def
  have hm : 0 < m := Nat.mul_pos hn (pow_pos hp.pos _)
  have hs : p ^ (r - 1) ∣ m := Dvd.intro_left n rfl
  have key := oeis_361883_SC hp hp5 hm hs
  have e1 : m * p = n * p ^ r := by
    rw [hm_def, mul_assoc, ← pow_succ]
    congr 2
    omega
  have e2 : 3 * (r - 1 + 1) = 3 * r := by omega
  rwa [e1, e2] at key
