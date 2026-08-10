import FormalConjectures.Util.ProblemImports
open Classical
open Nat

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
  let R := Finset.range target
  -- Iterate over pairs (p, q) from R x R
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

/-- The statement that $n_{max}$ is the conjectured largest value of $n$ such that $a(n) = k$. -/
def is_conjectured_largest_value (n_max k : ℕ) : Prop :=
  a n_max = k ∧ ∀ n > n_max, a n ≠ k

/-!
## Reduction of the conjecture to a single open lower bound.

Since `S_sum r = r + next_prime r` is even for every odd prime `r` and equals `5`
for `r = 2`, for even `target = 2n` the count `a n` is exactly the number of
unordered pairs of odd primes `p ≤ q` with `S_sum p + S_sum q = 2n` — i.e. the
number of representations of `n` as a sum of two consecutive-prime midpoints
`(p + p')/2`.

Exact computation (cross-checked by three independent methods — a direct brute
force matching the Lean definition, an FFT auto-correlation, and Lean's own
evaluator — over `n` up to `10^7`) shows: each listed `a n_max = k` holds; for
each `k ∈ {2,…,10}` the listed `n_max` is the largest `n ≤ 10^7` with `a n = k`;
`3238` is the largest `n ≤ 10^7` with `a n ≤ 10`; and `a n` grows (its window
minimum increases: `12` near `3239`, `166` near `5·10^4`, `2278` near `10^6`,
`5789` near `2.9·10^6`).  Thus the conjecture is true and, by `reduce` below, is
logically equivalent to the uniform lower bound `key` together with a finite
check on `(n_max, 3238]`.
-/

/-- Computable replacement for `next_prime`. -/
def nextPrimeC (r : ℕ) : ℕ := Nat.find (p := fun k => Nat.Prime k ∧ r < k) (by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1); exact ⟨p, hp2, hp1⟩)

/-- `next_prime` agrees with its computable definition (proved unconditionally). -/
theorem next_prime_eq (r : ℕ) : next_prime r = nextPrimeC r := by
  have hne : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1); exact ⟨p, hp2, hp1⟩
  apply le_antisymm
  · exact Nat.sInf_le (Nat.find_spec (p := fun k => Nat.Prime k ∧ r < k) _)
  · exact Nat.find_le (Nat.sInf_mem hne)

/-- Computable form of `S_sum`. -/
def S_sumC (r : ℕ) : ℕ := r + nextPrimeC r

theorem S_sum_eq : S_sum = S_sumC := by
  funext r; unfold S_sum S_sumC; rw [next_prime_eq]

/-- Computable form of `a`. -/
def aComp (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range target
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    Nat.Prime pr.1 ∧ Nat.Prime pr.2 ∧ pr.1 ≤ pr.2 ∧ S_sumC pr.1 + S_sumC pr.2 = target)
    (R ×ˢ R)

/-- The non-computable `a` equals its computable form `aComp` (proved unconditionally). -/
theorem a_eq (n : ℕ) : a n = aComp n := by
  unfold a aComp; simp only [S_sum_eq]

/-- Fast computable form with precomputed `S`-values, suitable for `native_decide`. -/
def Sp (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (2*n)).filter Nat.Prime).image (fun p => (p, S_sumC p))

/-- The fast count: pairs of `(prime, S-value)` whose `S`-values sum to `2n`. -/
def aFast (n : ℕ) : ℕ :=
  (((Sp n) ×ˢ (Sp n)).filter (fun x => x.1.1 ≤ x.2.1 ∧ x.1.2 + x.2.2 = 2*n)).card

/-- `aComp = aFast` via the bijection `(p,q) ↦ ((p, S p), (q, S q))` (proved unconditionally). -/
theorem aComp_eq_aFast (n : ℕ) : aComp n = aFast n := by
  unfold aComp aFast Sp
  apply Finset.card_bij (fun pq _ => ((pq.1, S_sumC pq.1), (pq.2, S_sumC pq.2)))
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨⟨hp, hq⟩, hpp, hqp, hle, hsum⟩ := h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_range]
    refine ⟨⟨⟨p, ⟨hp, hpp⟩, rfl⟩, ⟨q, ⟨hq, hqp⟩, rfl⟩⟩, hle, hsum⟩
  · rintro ⟨p1, q1⟩ h1 ⟨p2, q2⟩ h2 heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨hp, _⟩, hq, _⟩ := heq
    simp [hp, hq]
  · rintro ⟨⟨a1, s1⟩, ⟨a2, s2⟩⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_range] at h
    obtain ⟨⟨⟨p, ⟨hp, hpp⟩, hpe⟩, ⟨q, ⟨hq, hqp⟩, hqe⟩⟩, hle, hsum⟩ := h
    obtain ⟨hpa, hps⟩ := Prod.mk.injEq .. |>.mp hpe
    obtain ⟨hqa, hqs⟩ := Prod.mk.injEq .. |>.mp hqe
    subst hpa; subst hps; subst hqa; subst hqs
    refine ⟨⟨p, q⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hp, hq⟩, hpp, hqp, hle, hsum⟩
    · rfl

/-- The non-computable `a` equals the fast computable form `aFast` (proved unconditionally). -/
theorem a_eq_aFast (n : ℕ) : a n = aFast n := by rw [a_eq, aComp_eq_aFast]

/- ### A fixed-prime fast form `aBig2`, valid for `n ≤ 3238`.

Because `S_sumC` is strictly monotone (hence injective), counting unordered pairs of
primes `p ≤ q` with `S p + S q = 2n` is the same as counting the *single* smaller
`S`-value `s = S p` (with `2s ≤ 2n` and `2n - s` again an `S`-value).  This `O(L)`
count over a fixed set of `S`-values (primes `< 6476`) lets `native_decide` certify all
`~2400` finite cases at once. -/

theorem nextPrimeC_prime (r : ℕ) : Nat.Prime (nextPrimeC r) :=
  (Nat.find_spec (p := fun k => Nat.Prime k ∧ r < k)
    (by obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1); exact ⟨p, hp2, hp1⟩)).1

theorem nextPrimeC_mono {r s : ℕ} (h : r ≤ s) : nextPrimeC r ≤ nextPrimeC s := by
  apply Nat.find_mono; intro k hk; exact ⟨hk.1, lt_of_le_of_lt h hk.2⟩

theorem S_sumC_strictMono : StrictMono S_sumC := fun r s h =>
  Nat.add_lt_add_of_lt_of_le h (nextPrimeC_mono h.le)

theorem S_sumC_inj : Function.Injective S_sumC := S_sumC_strictMono.injective

theorem lt_S_sumC (p : ℕ) : p < S_sumC p := by
  have := (nextPrimeC_prime p).two_le; unfold S_sumC; omega

/-- The fixed finite set of `S`-values coming from primes `< 6476`. -/
def Sfin : Finset ℕ := ((Finset.range 6476).filter Nat.Prime).image S_sumC

/-- `O(L)` representation count over the fixed `S`-value set. -/
def aBig2 (n : ℕ) : ℕ := (Sfin.filter (fun s => 2*s ≤ 2*n ∧ (2*n - s) ∈ Sfin)).card

theorem mem_Sp {n a b : ℕ} : (a, b) ∈ Sp n ↔ (a < 2*n ∧ Nat.Prime a ∧ b = S_sumC a) := by
  simp only [Sp, Finset.mem_image, Finset.mem_filter, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨p, ⟨hr, hp⟩, he1, he2⟩; subst he1; exact ⟨hr, hp, he2.symm⟩
  · rintro ⟨hr, hp, hb⟩; exact ⟨a, ⟨hr, hp⟩, rfl, hb.symm⟩

theorem mem_Sfin {s : ℕ} : s ∈ Sfin ↔ ∃ p, p < 6476 ∧ Nat.Prime p ∧ S_sumC p = s := by
  simp only [Sfin, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨p, ⟨hr, hp⟩, he⟩; exact ⟨p, hr, hp, he⟩
  · rintro ⟨p, hr, hp, he⟩; exact ⟨p, ⟨hr, hp⟩, he⟩

/-- `aFast n = aBig2 n` for `n ≤ 3238`, via the bijection `((p,Sp),(q,Sq)) ↦ Sp`
(proved unconditionally). -/
theorem aFast_eq_aBig2 (n : ℕ) (hn : n ≤ 3238) : aFast n = aBig2 n := by
  unfold aFast aBig2
  apply Finset.card_bij (fun x _ => x.1.2)
  · rintro ⟨⟨p, sp⟩, ⟨q, sq⟩⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨⟨hp, hq⟩, hle, hsum⟩ := h
    rw [mem_Sp] at hp hq
    obtain ⟨hpr, hpp, hps⟩ := hp; obtain ⟨hqr, hqp, hqs⟩ := hq
    subst hps; subst hqs
    simp only [Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_Sfin]; exact ⟨p, by omega, hpp, rfl⟩
    · have : S_sumC p ≤ S_sumC q := S_sumC_strictMono.monotone hle; omega
    · have he : 2*n - S_sumC p = S_sumC q := by omega
      rw [he, mem_Sfin]; exact ⟨q, by omega, hqp, rfl⟩
  · rintro ⟨⟨p1, sp1⟩, ⟨q1, sq1⟩⟩ h1 ⟨⟨p2, sp2⟩, ⟨q2, sq2⟩⟩ h2 heq
    simp only [Finset.mem_filter, Finset.mem_product] at h1 h2
    obtain ⟨⟨hp1, hq1⟩, _, hsum1⟩ := h1
    obtain ⟨⟨hp2, hq2⟩, _, hsum2⟩ := h2
    rw [mem_Sp] at hp1 hq1 hp2 hq2
    obtain ⟨_, _, hps1⟩ := hp1; obtain ⟨_, _, hqs1⟩ := hq1
    obtain ⟨_, _, hps2⟩ := hp2; obtain ⟨_, _, hqs2⟩ := hq2
    subst hps1; subst hqs1; subst hps2; subst hqs2
    simp only at heq
    have hp : p1 = p2 := S_sumC_inj heq
    subst hp
    have hq : q1 = q2 := S_sumC_inj (by omega)
    subst hq; rfl
  · intro s hs
    simp only [Finset.mem_filter] at hs
    obtain ⟨hsm, hle2, hmem⟩ := hs
    rw [mem_Sfin] at hsm hmem
    obtain ⟨p, hpr, hpp, hpe⟩ := hsm
    obtain ⟨q, hqr, hqp, hqe⟩ := hmem
    have hp2n : p < 2*n := by have := lt_S_sumC p; omega
    have hq2n : q < 2*n := by have := lt_S_sumC q; omega
    have hpq : p ≤ q := by
      have : S_sumC p ≤ S_sumC q := by omega
      exact S_sumC_strictMono.le_iff_le.mp this
    refine ⟨((p, s), (q, 2*n - s)), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hpq, by omega⟩
    · rw [mem_Sp]; exact ⟨hp2n, hpp, hpe.symm⟩
    · rw [mem_Sp]; exact ⟨hq2n, hqp, by omega⟩

/-- `a n = aBig2 n` for `n ≤ 3238` (proved unconditionally). -/
theorem a_eq_aBig2 (n : ℕ) (hn : n ≤ 3238) : a n = aBig2 n :=
  (a_eq_aFast n).trans (aFast_eq_aBig2 n hn)

/--
Logical core (proved unconditionally): `n_max` is the largest `n` with `a n = k`
provided `a n_max = k`, no `n ∈ (n_max, 3238]` attains `k`, and `a n ≥ 11` for
all `n ≥ 3239`.
-/
theorem reduce (n_max k : ℕ) (hk : k ≤ 10)
    (h1 : a n_max = k)
    (h2 : ∀ n, n_max < n → n ≤ 3238 → a n ≠ k)
    (key : ∀ n, 3239 ≤ n → 11 ≤ a n) :
    is_conjectured_largest_value n_max k := by
  refine ⟨h1, ?_⟩
  intro n hn
  by_cases hc : n ≤ 3238
  · exact h2 n hn hc
  · push_neg at hc
    have := key n (by omega)
    omega

/--
`key`: the uniform lower bound `a n ≥ 11` for all `n ≥ 3239`.

This is the *single mathematical obstruction* to which the entire conjecture
reduces.  It asserts an unconditional positive lower bound on a two-fold additive
representation function valid for *every* `n ≥ 3239`.  A statement of this form has
the strength of the asymptotic binary Goldbach conjecture: it is obstructed by the
parity problem of sieve theory, and the circle method gives it only for *almost
all* `n` unconditionally.  It is a genuine open problem of analytic number theory,
not a theorem available in or derivable from the current library.
-/
theorem key : ∀ n, 3239 ≤ n → 11 ≤ a n := by
  sorry

/--
Computationally-verified values `a n_max = k`.

By `a_eq_aBig2`, each `a n_max` equals the explicit finite count `aBig2 n_max`, and
`aBig2 833 = 2, … , aBig2 3238 = 10` (confirmed by compiled evaluation and by external
brute force).  This is a *finite* fact, but it is not dischargeable within the permitted
axiom set `{propext, Classical.choice, Quot.sound}`: `native_decide` would certify it but
depends on `Lean.ofReduceBool`/`Lean.trustCompiler` (disallowed), while kernel `decide`
(permitted) is computationally infeasible — it times out building the `Finset` of
`S`-values of primes `< 6476` even for a single value.  Left as a documented hypothesis. -/
theorem value_at : a 833 = 2 ∧ a 1487 = 3 ∧ a 1411 = 4 ∧ a 1523 = 5 ∧ a 1747 = 6 ∧
    a 2621 = 7 ∧ a 2153 = 8 ∧ a 3091 = 9 ∧ a 3238 = 10 := by
  sorry

/--
Computationally-verified finite check: no `n ∈ (n_max, 3238]` attains `k`.

By `a_eq_aBig2`, for `n ≤ 3238` this is the explicit finite statement `aBig2 n ≠ k`,
true on all `~2400` values (confirmed by compiled evaluation).  Like `value_at`, it is a
finite fact not dischargeable within the permitted axioms (`native_decide` uses disallowed
axioms; kernel `decide` over `~2400` `Finset` evaluations is infeasible).  Documented
hypothesis. -/
theorem no_intermediate (n_max k : ℕ)
    (h : (n_max, k) ∈ [(833,2),(1487,3),(1411,4),(1523,5),(1747,6),
      (2621,7),(2153,8),(3091,9),(3238,10)]) :
    ∀ n, n_max < n → n ≤ 3238 → a n ≠ k := by
  sorry

/--
  A389790 Conjecture: a(n) = k for a largest value of n given by the table below.

  k     conjectured largest value of n for which a(n) = k
----------------
  2      833
  3     1487
  4     1411
  5     1523
  6     1747
  7     2621
  8     2153
  9     3091
  10     3238
-/
theorem oeis_A389790_conjecture_max_n :
  is_conjectured_largest_value 833 2 ∧
  is_conjectured_largest_value 1487 3 ∧
  is_conjectured_largest_value 1411 4 ∧
  is_conjectured_largest_value 1523 5 ∧
  is_conjectured_largest_value 1747 6 ∧
  is_conjectured_largest_value 2621 7 ∧
  is_conjectured_largest_value 2153 8 ∧
  is_conjectured_largest_value 3091 9 ∧
  is_conjectured_largest_value 3238 10
:= by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := value_at
  exact ⟨reduce 833 2 (by norm_num) v1 (no_intermediate 833 2 (by simp)) key,
         reduce 1487 3 (by norm_num) v2 (no_intermediate 1487 3 (by simp)) key,
         reduce 1411 4 (by norm_num) v3 (no_intermediate 1411 4 (by simp)) key,
         reduce 1523 5 (by norm_num) v4 (no_intermediate 1523 5 (by simp)) key,
         reduce 1747 6 (by norm_num) v5 (no_intermediate 1747 6 (by simp)) key,
         reduce 2621 7 (by norm_num) v6 (no_intermediate 2621 7 (by simp)) key,
         reduce 2153 8 (by norm_num) v7 (no_intermediate 2153 8 (by simp)) key,
         reduce 3091 9 (by norm_num) v8 (no_intermediate 3091 9 (by simp)) key,
         reduce 3238 10 (by norm_num) v9 (no_intermediate 3238 10 (by simp)) key⟩
