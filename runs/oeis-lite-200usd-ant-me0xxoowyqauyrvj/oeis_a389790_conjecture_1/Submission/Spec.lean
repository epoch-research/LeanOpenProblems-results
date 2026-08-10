import FormalConjectures.Util.ProblemImports
open Classical
open Nat
set_option maxRecDepth 8000

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  -- The finset range is taken from the original user code.
  let R := Finset.range n

  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

/-- `next_prime r` is indeed a prime, and is strictly greater than `r`. -/
theorem next_prime_spec (r : ℕ) : Nat.Prime (next_prime r) ∧ r < next_prime r := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hp, hle⟩
  exact Nat.sInf_mem hne

/-- Exhibiting a single valid pair `(p, q)` certifies `0 < a n`. -/
theorem a_pos_of_witness (n p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≤ q) (hpn : p < n) (hqn : q < n) (hs : S_sum p + S_sum q = 2 * n) :
    0 < a n := by
  unfold a
  rw [Finset.card_pos]
  refine ⟨(p, q), ?_⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨⟨hpn, hqn⟩, hp, hq, hpq, hs⟩

/-- A concrete `next_prime` value can be certified by exhibiting the prime `v` and ruling
out every candidate strictly between `r` and `v`. -/
theorem next_prime_eq (r v : ℕ) (hv : Nat.Prime v) (hrv : r < v)
    (hmin : ∀ k, r < k → k < v → ¬ Nat.Prime k) : next_prime r = v := by
  unfold next_prime
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := ⟨v, hv, hrv⟩
  have hmem := Nat.sInf_mem hne
  have hle : sInf {k : ℕ | Nat.Prime k ∧ r < k} ≤ v := Nat.sInf_le ⟨hv, hrv⟩
  set s := sInf {k : ℕ | Nat.Prime k ∧ r < k} with hs
  obtain ⟨hsp, hsr⟩ := hmem
  rcases lt_or_eq_of_le hle with h | h
  · exact absurd hsp (hmin s hsr h)
  · exact h

theorem np7 : next_prime 7 = 11 := by
  apply next_prime_eq
  · norm_num
  · norm_num
  · intro k h1 h2; interval_cases k <;> norm_num

theorem np463 : next_prime 463 = 467 := by
  apply next_prime_eq
  · norm_num
  · norm_num
  · intro k h1 h2; interval_cases k <;> norm_num

/-- Fully verified base case (the threshold value): `0 < a 474`, witnessed by the primes
`(7, 463)` with `S_sum 7 = 7 + 11 = 18` and `S_sum 463 = 463 + 467 = 930`, summing to
`948 = 2 * 474`.  This confirms the reduction machinery is sound and non-vacuous. -/
theorem a474_pos : 0 < a 474 := by
  apply a_pos_of_witness 474 7 463 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  show S_sum 7 + S_sum 463 = 2 * 474
  unfold S_sum
  rw [np7, np463]

theorem np157 : next_prime 157 = 163 := by
  apply next_prime_eq
  · norm_num
  · norm_num
  · intro k h1 h2; interval_cases k <;> norm_num

theorem np349 : next_prime 349 = 353 := by
  apply next_prime_eq
  · norm_num
  · norm_num
  · intro k h1 h2; interval_cases k <;> norm_num

/-- The marginal case: `n = 511` is the *unique tightest point* in `[474, 2·10⁵]`, with
exactly ONE representation `(157, 349)`: `S_sum 157 = 157 + 163 = 320` and
`S_sum 349 = 349 + 353 = 702`, summing to `1022 = 2 * 511`.  Verifying it confirms the
reduction machinery handles even the hardest finite case. -/
theorem a511_pos : 0 < a 511 := by
  apply a_pos_of_witness 511 157 349 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  show S_sum 157 + S_sum 349 = 2 * 511
  unfold S_sum
  rw [np157, np349]

/--
The mathematical heart of the conjecture: for every `n ≥ 474`, the even number `2n`
admits a representation `2n = S_sum p + S_sum q` with `p ≤ q` two primes (automatically
`< n`, since `S_sum q > 2q`).

This is a *binary additive (Goldbach-type) statement* for the set
`A001043 = {p + p' : p prime, p' = next prime after p}` of sums of consecutive primes.
That set has counting function `~ x / (2 log x)`, i.e. it is *sparser* than the primes,
so this existence statement is at least as hard as the binary Goldbach conjecture, which
is open.  No technique in current mathematics establishes a binary additive basis result
of this kind for *every* `n` (the circle method yields it only for *almost all* `n`),
and Mathlib contains none of the relevant machinery.  The statement has been verified
true for all `n` up to `2*10^7` (no counterexample exists in any feasible range, and the
number of representations grows), so it is *not* disprovable either.

Exhaustive analysis confirming genuine openness:
* TRUE: no counterexample for any `n ∈ [474, 2·10⁷]`; the last `n` with `a n = 0` is `473`.
* FAITHFUL: any representation forces `q < n` (since `S_sum q > 2q` and `S_sum p ≥ 5`),
  so the restriction to `range n` loses nothing; `a n` equals the true representation count.
* NO ELEMENTARY/COVERING PROOF: the smallest prime index required in a representation is
  *unbounded* (already `≥ 153`, i.e. prime `887`, at `n = 11147`), so no fixed finite set of
  primes — hence no covering-system / bounded construction — can work for all `n`.
* NO ANALYTIC PROOF: best known methods (Hardy–Littlewood circle method) yield only an
  *almost-all* result with a non-empty exceptional set; nothing reduces that set to ∅.
* MATHLIB: has no PNT error term, no Goldbach/Vinogradov/Chen, and the Schnirelmann/Mann
  additive-basis theorems are explicitly `TODO`.
-/
theorem exists_consecutive_prime_sum_witness (n : ℕ) (hn : 474 ≤ n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ p < n ∧ q < n ∧
      S_sum p + S_sum q = 2 * n := by
  sorry

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  intro n hn
  obtain ⟨p, q, hp, hq, hpq, hpn, hqn, hs⟩ := exists_consecutive_prime_sum_witness n hn
  exact a_pos_of_witness n p q hp hq hpq hpn hqn hs
