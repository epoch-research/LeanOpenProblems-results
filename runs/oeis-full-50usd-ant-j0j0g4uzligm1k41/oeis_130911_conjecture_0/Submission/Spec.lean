import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 10000

/--
A130911: $a(n)$ is the number of primes with odd binary weight among the first $n$ primes minus the number with an even binary weight.
Primes with odd binary weight are called odious primes (A027697); primes with even binary weight are called evil primes (A027699).
$$a(n) = \sum_{k=1}^n \left( \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is odd}\}} - \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is even}\}} \right)$$
where $p_k$ is the $k$-th prime number.
-/
noncomputable def A130911 (n : ℕ) : ℤ :=
  -- The binary weight (popcount) is the sum of digits in base 2.
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum

  -- The function to be summed: +1 for odd weight, -1 for even weight.
  let weight_parity_sign (p : ℕ) : ℤ :=
    -- Nat.bodd returns true if the number is odd.
    if (binary_weight p).bodd then 1 else -1

  -- Sum over the indices i from 0 to n-1, corresponding to the first n primes.
  Finset.sum (Finset.range n) fun i =>
    let p_i := Nat.nth Nat.Prime i
    weight_parity_sign p_i

/-!
### Reduction of Shevelev's conjecture

We give a complete proof **modulo a single isolated lemma** (`shevelev_tail`),
which is precisely the open analytic core of Shevelev's conjecture.

Write `s(p)` for the binary digit sum (popcount) of `p`.  Then `A130911`
satisfies the recurrence `A130911 (n+1) = A130911 n + wsign (pₙ)` where
`wsign p = +1` if `p` is odious (odd `s(p)`) and `-1` if `p` is evil.  All finite
base cases `A130911 0, …, A130911 10` are evaluated rigorously below, giving
`A130911 n ≥ 0` for `4 ≤ n ≤ 10`.  The conjecture therefore reduces exactly to
`A130911 n ≥ 0` for `n > 10`.

That residual statement is the open content: it asserts pointwise nonnegativity
of the partial sums of the Thue–Morse sequence `(-1)^{s(p)}` along the primes.
Establishing it requires the Mauduit–Rivat theorem together with the *sign* of
its second-order term and effective bounds — none of which is available in
Mathlib.  A strong-induction attempt fails because the invariant `a(n) ≥ 1`
cannot be maintained: each increment `wsign (pₙ) = ±1` depends unpredictably on
the popcount parity of the `n`-th prime, which is exactly the quantity the open
analytic theory controls.
-/

/-- The signed weight contributed by a prime `p`: `+1` if `p` is odious
(odd binary weight), `-1` if `p` is evil (even binary weight). -/
noncomputable def weightSign (p : ℕ) : ℤ :=
  if ((Nat.digits 2 p).sum).bodd then 1 else -1

theorem A130911_eq_sum (n : ℕ) :
    A130911 n = ∑ i ∈ Finset.range n, weightSign (Nat.nth Nat.Prime i) := rfl

/-- The partial-sum recurrence. -/
theorem A130911_succ (n : ℕ) :
    A130911 (n + 1) = A130911 n + weightSign (Nat.nth Nat.Prime n) := by
  simp only [A130911, weightSign, Finset.sum_range_succ]

private theorem wsv (p s : ℕ) (hp : (Nat.digits 2 p).sum = s) :
    weightSign p = if s.bodd then 1 else -1 := by rw [weightSign, hp]

local macro "ds" : tactic =>
  `(tactic| norm_num [Nat.digits_def' (b := 2) (by norm_num : 2 ≤ 2)])

private theorem wp0 : weightSign (Nat.nth Nat.Prime 0) = 1 := by
  rw [Nat.nth_prime_zero_eq_two, wsv 2 1 (by ds)]; decide
private theorem wp1 : weightSign (Nat.nth Nat.Prime 1) = -1 := by
  rw [Nat.nth_prime_one_eq_three, wsv 3 2 (by ds)]; decide
private theorem wp2 : weightSign (Nat.nth Nat.Prime 2) = -1 := by
  rw [Nat.nth_prime_two_eq_five, wsv 5 2 (by ds)]; decide
private theorem wp3 : weightSign (Nat.nth Nat.Prime 3) = 1 := by
  rw [Nat.nth_prime_three_eq_seven, wsv 7 3 (by ds)]; decide
private theorem wp4 : weightSign (Nat.nth Nat.Prime 4) = 1 := by
  rw [Nat.nth_prime_four_eq_eleven, wsv 11 3 (by ds)]; decide
private theorem wp5 : weightSign (Nat.nth Nat.Prime 5) = 1 := by
  rw [(by simpa [(by decide : Nat.count Nat.Prime 13 = 5)] using
    Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num) : Nat.nth Nat.Prime 5 = 13),
    wsv 13 3 (by ds)]; decide
private theorem wp6 : weightSign (Nat.nth Nat.Prime 6) = -1 := by
  rw [(by simpa [(by decide : Nat.count Nat.Prime 17 = 6)] using
    Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num) : Nat.nth Nat.Prime 6 = 17),
    wsv 17 2 (by ds)]; decide
private theorem wp7 : weightSign (Nat.nth Nat.Prime 7) = 1 := by
  rw [(by simpa [(by decide : Nat.count Nat.Prime 19 = 7)] using
    Nat.nth_count (p := Nat.Prime) (n := 19) (by norm_num) : Nat.nth Nat.Prime 7 = 19),
    wsv 19 3 (by ds)]; decide
private theorem wp8 : weightSign (Nat.nth Nat.Prime 8) = -1 := by
  rw [(by simpa [(by decide : Nat.count Nat.Prime 23 = 8)] using
    Nat.nth_count (p := Nat.Prime) (n := 23) (by norm_num) : Nat.nth Nat.Prime 8 = 23),
    wsv 23 4 (by ds)]; decide
private theorem wp9 : weightSign (Nat.nth Nat.Prime 9) = -1 := by
  rw [(by simpa [(by decide : Nat.count Nat.Prime 29 = 9)] using
    Nat.nth_count (p := Nat.Prime) (n := 29) (by norm_num) : Nat.nth Nat.Prime 9 = 29),
    wsv 29 4 (by ds)]; decide

theorem A130911_0 : A130911 0 = 0 := rfl
theorem A130911_4 : A130911 4 = 0 := by
  rw [show (4:ℕ)=3+1 from rfl, A130911_succ,
      show (3:ℕ)=2+1 from rfl, A130911_succ,
      show (2:ℕ)=1+1 from rfl, A130911_succ,
      show (1:ℕ)=0+1 from rfl, A130911_succ, A130911_0, wp0, wp1, wp2, wp3]; ring
theorem A130911_5 : A130911 5 = 1 := by
  rw [show (5:ℕ)=4+1 from rfl, A130911_succ, A130911_4, wp4]; ring
theorem A130911_6 : A130911 6 = 2 := by
  rw [show (6:ℕ)=5+1 from rfl, A130911_succ, A130911_5, wp5]; ring
theorem A130911_7 : A130911 7 = 1 := by
  rw [show (7:ℕ)=6+1 from rfl, A130911_succ, A130911_6, wp6]; ring
theorem A130911_8 : A130911 8 = 2 := by
  rw [show (8:ℕ)=7+1 from rfl, A130911_succ, A130911_7, wp7]; ring
theorem A130911_9 : A130911 9 = 1 := by
  rw [show (9:ℕ)=8+1 from rfl, A130911_succ, A130911_8, wp8]; ring
theorem A130911_10 : A130911 10 = 0 := by
  rw [show (10:ℕ)=9+1 from rfl, A130911_succ, A130911_9, wp9]; ring

/-- **The open analytic core of Shevelev's conjecture** (OEIS A130911): pointwise
nonnegativity of the Thue–Morse partial sums along the primes for `n > 10`.  This
is an unproven statement requiring the Mauduit–Rivat theorem and the sign of its
second-order term, machinery not available in Mathlib. -/
theorem shevelev_tail : ∀ n, 10 < n → 0 ≤ A130911 n := sorry

/-- Shevelev conjectures that a(n) >= 0 for n > 3. -/
theorem oeis_130911_conjecture_0 (n : ℕ) (h : n > 3) : A130911 n ≥ 0 := by
  rcases Nat.lt_or_ge n 11 with h2 | h2
  · interval_cases n <;>
      simp only [ge_iff_le, A130911_4, A130911_5, A130911_6, A130911_7, A130911_8,
        A130911_9, A130911_10] <;> norm_num
  · exact shevelev_tail n (by omega)
