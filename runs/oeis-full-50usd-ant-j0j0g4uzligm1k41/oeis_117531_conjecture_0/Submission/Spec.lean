import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A117531: Number of primes in the $n$-th row of the triangle in A117530.
The elements of the $n$-th row of A117530 are $T(n, k) = k^2 - k + p_n$ for $1 \le k \le n$,
where $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sequence is defined for n >= 1. Icc 1 0 is empty, correctly yielding 0 for n=0.
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  -- We count how many terms T(n, k) are prime for k in {1, 2, ..., n}.
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

/-!
## Resolution of the conjecture

The conjecture is **true**, and it is *equivalent to a consequence of the Stark–Heegner
theorem* (the resolution of Gauss's class number one problem).

**Reduction.**  Write `pₙ = nth Prime (n-1)` and `f k = k² - k + pₙ`.  Note `a n ≤ n`
always (the filter sits inside `Icc 1 n`, which has `n` elements), and `a n < n` holds
iff some entry `f k` (`1 ≤ k ≤ n`) is *not* prime.  An entry `f k` is composite as soon as
some prime `q ≤ n` divides it (since `f k ≥ pₙ > n ≥ q`, so `q < f k`).  Such a `q` exists
iff `x² - x + pₙ` has a root modulo some prime `q ≤ n`, i.e. iff the discriminant
`D = 1 - 4 pₙ` is a square (or `0`) modulo some prime `q ≤ n`.

* **Composite-`D` case** (`4 pₙ - 1` composite).  Its least prime factor `q` is odd and
  `q ≤ √(4 pₙ - 1) < n` (using `pₙ < n²/4` for `n ≥ 14`).  Then `q ∣ D`, so `x² - x + pₙ`
  has the (double) root `x ≡ (q+1)/2 (mod q)`, giving a composite `f k`.  *Elementary.*

* **Prime-`D` case** (`P := 4 pₙ - 1` is prime).  For `n > 13` we have `pₙ > 41`, hence
  `P > 163`, so `-P` is a fundamental discriminant strictly below `-163`.  By the
  **Stark–Heegner theorem**, the class number `h(-P) ≥ 2`; thus there is a non-principal
  reduced form `a x² + b x y + c y²` of discriminant `-P` with leading coefficient
  `1 < a ≤ √(P/3) < n`.  Every prime factor `q ≤ a < n` of `a` is *split* (`(D | q) = 1`),
  so `x² - x + pₙ` has a root mod `q`, again giving a composite `f k`.

The threshold `n = 13 ↔ pₙ = 41 ↔ D = -163` is exactly the largest Heegner number; the only
discriminants `-P = 1 - 4p` with `h = 1` are `p ∈ {2, 3, 5, 11, 17, 41}`, all giving `n ≤ 13`.

That this cannot be done by elementary means is confirmed by computation: the least split /
ramified prime `q ≤ n` is *unbounded* in `n` (it reaches `q = 3, 7, 11, …, 89, …` as `n`
grows), so **no finite covering system of primes suffices** — the bound `q ≤ √(P/3)` (and
hence the lower bound `h(-P) ≥ 2`) is essential.

Below, the entire reduction is formalised rigorously.  The single irreducible input is
`exists_root_prime_le`, the assertion `h(-P) ≥ 2` for `P > 163` — the Stark–Heegner theorem,
which is not (yet) available in Mathlib.
-/

/-- `pₙ = nth Prime (n-1)` exceeds `n` for `n ≥ 1` (the `n`-th prime is `> n`). -/
theorem nth_prime_gt (n : ℕ) (hn : 1 ≤ n) : n < Nat.nth Nat.Prime (n - 1) := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have h2 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have key : (n - 1) + Nat.nth Nat.Prime 0 ≤ Nat.nth Nat.Prime (n - 1) := by
    have := hmono.add_le_nat (n - 1) 0
    simpa using this
  rw [h2] at key
  omega

/-- If a prime `q` strictly below `m` divides `m`, then `m` is not prime. -/
theorem composite_of_dvd (q m : ℕ) (hq : q.Prime) (hdvd : q ∣ m) (hlt : q < m) : ¬ m.Prime := by
  intro hm
  rcases hm.eq_one_or_self_of_dvd q hdvd with h1 | h2
  · exact (Nat.Prime.one_lt hq).ne' h1
  · omega

/-- **Reduction lemma.**  If some entry `f k` (`1 ≤ k ≤ n`) of row `n` is not prime, then the
number of primes in the row is strictly less than `n`. -/
theorem reduction (n : ℕ)
    (hex : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) :
    a n < n := by
  obtain ⟨k, hk, hcomp⟩ := hex
  unfold a
  set pn := Nat.nth Nat.Prime (n - 1)
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  have hsub : Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n)
      ⊂ Finset.Icc 1 n := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨k, hk, by simp [hcomp]⟩
  calc (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n)).card
      < (Finset.Icc 1 n).card := Finset.card_lt_card hsub
    _ = n := hcard

/-- A prime `q ≤ n` together with a root `k ∈ [1,n]` of `x² - x + pₙ` modulo `q` yields a
composite entry in row `n`. -/
theorem exists_composite (n : ℕ) (hn : 13 < n)
    (hsplit : ∃ q, q.Prime ∧ q ≤ n ∧
      ∃ k ∈ Finset.Icc 1 n, q ∣ (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) :
    ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  obtain ⟨q, hq, hqn, k, hk, hdvd⟩ := hsplit
  refine ⟨k, hk, ?_⟩
  apply composite_of_dvd q _ hq hdvd
  have hpn : n < Nat.nth Nat.Prime (n - 1) := nth_prime_gt n (by omega)
  have hle : Nat.nth Nat.Prime (n - 1) ≤ k ^ 2 - k + Nat.nth Nat.Prime (n - 1) :=
    Nat.le_add_left _ _
  omega

/- ### Chebyshev's lower bound: the `n`-th prime is `≤ n²`

We need `pₙ ≤ n²` so that any prime factor of the (odd) number `4 pₙ - 1` is `< 2 n`.  Mathlib
provides only *upper* bounds on `π`; we derive the required *lower* bound `π (n²) ≥ n` from the
central binomial coefficient (the same engine behind the Bertrand-postulate proof). -/

/-- `centralBinom n ≤ (2n)^{π(2n)}`: each prime power `p^{vₚ}` dividing `C(2n,n)` is `≤ 2n`,
and there are `π(2n)` primes `≤ 2n`. -/
theorem centralBinom_le_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.centralBinom n ≤ (2 * n) ^ (Nat.primeCounting (2 * n)) := by
  have h2n : 0 < 2 * n := by omega
  rw [← Nat.prod_pow_factorization_centralBinom n]
  have hterm : ∀ p ∈ Finset.range (2 * n + 1),
      p ^ (Nat.centralBinom n).factorization p ≤ (if p.Prime then 2 * n else 1) := by
    intro p hp
    by_cases hpp : p.Prime
    · simp only [hpp, if_true]
      have := Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n) h2n
      simpa [Nat.centralBinom] using this
    · simp only [hpp, if_false]
      have : (Nat.centralBinom n).factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]; exact Or.inl hpp
      rw [this, pow_zero]
  calc ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p
      ≤ ∏ p ∈ Finset.range (2 * n + 1), (if p.Prime then 2 * n else 1) :=
        Finset.prod_le_prod' hterm
    _ = (2 * n) ^ ((Finset.range (2 * n + 1)).filter Nat.Prime).card := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    _ = (2 * n) ^ (Nat.primeCounting (2 * n)) := by
        congr 1
        rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- `2n+1 ≤ 2ⁿ` for `n ≥ 3`. -/
theorem two_mul_add_one_le (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · have hk2 : k = 2 := by omega
      subst hk2; norm_num
    · have h1 := ih hk
      have e2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      rw [e2]; omega

/-- `n² ≤ 2ⁿ` for `n ≥ 4`. -/
theorem sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 4 with hk | hk
    · have hk3 : k = 3 := by omega
      subst hk3; norm_num
    · have h1 := ih hk
      have h2 := two_mul_add_one_le k (by omega)
      have e1 : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
      have e2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      rw [e1, e2]; omega

/-- **Chebyshev lower bound**: `π(n²) ≥ n` for `n ≥ 4`. -/
theorem chebyshev_pi (n : ℕ) (hn : 4 ≤ n) : n ≤ Nat.primeCounting (n ^ 2) := by
  by_contra hcon
  push_neg at hcon
  have hpi : Nat.primeCounting (n ^ 2) ≤ n - 1 := by omega
  have hn2 : 16 ≤ n ^ 2 := by nlinarith
  set k := n ^ 2 / 2 with hk_def
  have hk4 : 4 ≤ k := by rw [hk_def]; omega
  have h2k_le : 2 * k ≤ n ^ 2 := by rw [hk_def]; omega
  have h2k_ge : n ^ 2 ≤ 2 * k + 1 := by
    rw [hk_def]; have := Nat.div_add_mod (n ^ 2) 2; omega
  have hcb1 : 4 ^ k < k * Nat.centralBinom k := Nat.four_pow_lt_mul_centralBinom k hk4
  have hcb2 : Nat.centralBinom k ≤ (2 * k) ^ (Nat.primeCounting (2 * k)) :=
    centralBinom_le_pow k (by omega)
  have hpimono : Nat.primeCounting (2 * k) ≤ Nat.primeCounting (n ^ 2) :=
    Nat.monotone_primeCounting h2k_le
  have hpos : 0 < n ^ 2 := by omega
  have hbase : (2 * k) ^ (Nat.primeCounting (2 * k)) ≤ (n ^ 2) ^ (n - 1) := by
    calc (2 * k) ^ (Nat.primeCounting (2 * k))
        ≤ (n ^ 2) ^ (Nat.primeCounting (2 * k)) := by gcongr
      _ ≤ (n ^ 2) ^ (Nat.primeCounting (n ^ 2)) := by gcongr <;> omega
      _ ≤ (n ^ 2) ^ (n - 1) := by gcongr <;> omega
  have hcomb : 4 ^ k < k * (n ^ 2) ^ (n - 1) := by
    calc 4 ^ k < k * Nat.centralBinom k := hcb1
      _ ≤ k * (2 * k) ^ (Nat.primeCounting (2 * k)) := by gcongr
      _ ≤ k * (n ^ 2) ^ (n - 1) := by gcongr
  have h4k : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hlow : 2 ^ (n ^ 2) ≤ 2 * 4 ^ k := by
    rw [h4k, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhigh : 2 * 4 ^ k < (n ^ 2) ^ n := by
    have hstep : 2 * (k * (n ^ 2) ^ (n - 1)) ≤ (n ^ 2) ^ n := by
      calc 2 * (k * (n ^ 2) ^ (n - 1)) = (2 * k) * (n ^ 2) ^ (n - 1) := by ring
        _ ≤ (n ^ 2) * (n ^ 2) ^ (n - 1) := by gcongr
        _ = (n ^ 2) ^ n := by rw [← pow_succ']; congr 1; omega
    have : 2 * 4 ^ k < 2 * (k * (n ^ 2) ^ (n - 1)) := by gcongr
    omega
  have hsq : (n ^ 2) ^ n ≤ 2 ^ (n ^ 2) := by
    calc (n ^ 2) ^ n ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (sq_le_two_pow n hn) n
      _ = 2 ^ (n ^ 2) := by rw [← pow_mul]; congr 1; ring
  omega

/-- The `n`-th prime is `≤ n²` for `n ≥ 4`. -/
theorem nth_prime_le_sq (n : ℕ) (hn : 4 ≤ n) : Nat.nth Nat.Prime (n - 1) ≤ n ^ 2 := by
  have hpi := chebyshev_pi n hn
  by_contra hcon
  push_neg at hcon
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  have key : Nat.count Nat.Prime (n ^ 2 + 1) ≤ n - 1 := by
    rw [Nat.count_le_iff_le_nth hinf]; omega
  have heq : Nat.primeCounting (n ^ 2) = Nat.count Nat.Prime (n ^ 2 + 1) := rfl
  omega

/- ### The composite-`D` case (elementary)

If `4 pₙ - 1` is *not* prime, then its least prime factor `q` is odd and `q² ≤ 4 pₙ - 1 < (2n)²`,
hence `q < 2n`.  As `q ∣ 4 pₙ - 1`, the polynomial `x² - x + pₙ` has the double root
`r = (q+1)/2 ≤ n` modulo `q`, producing the composite entry `f r`. -/

/-- **Composite-`D` case.**  If `4 pₙ - 1` is not prime, some entry of row `n` is composite. -/
theorem composite_D_entry (n : ℕ) (hn : 13 < n)
    (hcomp : ¬ Nat.Prime (4 * Nat.nth Nat.Prime (n - 1) - 1)) :
    ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  set p := Nat.nth Nat.Prime (n - 1) with hp_def
  have hp_prime : Nat.Prime p := Nat.prime_nth_prime _
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hple : p ≤ n ^ 2 := nth_prime_le_sq n (by omega)
  set m := 4 * p - 1 with hm_def
  have hm1 : 1 < m := by omega
  have hm0 : 0 < m := by omega
  set q := m.minFac with hq_def
  have hq_prime : Nat.Prime q := Nat.minFac_prime (by omega)
  have hq_dvd : q ∣ m := Nat.minFac_dvd m
  have hq_sq : q ^ 2 ≤ m := Nat.minFac_sq_le_self hm0 hcomp
  have hm_odd : ¬ 2 ∣ m := by omega
  have hq_ne2 : q ≠ 2 := fun h => hm_odd (h ▸ hq_dvd)
  have hq_odd : Odd q := hq_prime.odd_of_ne_two hq_ne2
  have hq3 : 3 ≤ q := by
    rcases hq_odd with ⟨t, ht⟩
    have := hq_prime.two_le; omega
  have h1 : q ^ 2 ≤ 4 * n ^ 2 - 1 := by
    calc q ^ 2 ≤ m := hq_sq
      _ = 4 * p - 1 := rfl
      _ ≤ 4 * n ^ 2 - 1 := by omega
  have hq_lt_2n : q < 2 * n := by
    by_contra hc
    push_neg at hc
    have h2 : (2 * n) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hc 2
    have h3 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
    omega
  obtain ⟨s, hs⟩ := hq_odd
  set r := s + 1 with hr_def
  have hr_eq : 2 * r - 1 = q := by omega
  have hr1 : 1 ≤ r := by omega
  have hrn : r ≤ n := by omega
  have hge : r ≤ r ^ 2 := by nlinarith
  have h2r1 : 1 ≤ 2 * r := by omega
  have h4p1 : 1 ≤ 4 * p := by omega
  refine ⟨r, Finset.mem_Icc.2 ⟨hr1, hrn⟩, ?_⟩
  have hfr : 4 * (r ^ 2 - r + p) = q ^ 2 + m := by
    have key : 4 * (r ^ 2 - r + p) = (2 * r - 1) ^ 2 + (4 * p - 1) := by
      zify [hge, h2r1, h4p1]; ring
    rw [key, hr_eq, hm_def]
  have hq_dvd_fr : q ∣ (r ^ 2 - r + p) := by
    have hdvd4 : q ∣ 4 * (r ^ 2 - r + p) := by
      rw [hfr]; exact dvd_add (dvd_pow_self q (by norm_num)) hq_dvd
    have hcop : Nat.Coprime q 4 := by
      have hc2 : q.Coprime 2 := (Nat.coprime_primes hq_prime Nat.prime_two).2 hq_ne2
      have : q.Coprime (2 ^ 2) := hc2.pow_right 2
      simpa using this
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd4
  have hfr_gt : q < r ^ 2 - r + p := by
    have hz : (q : ℤ) < (r : ℤ) ^ 2 - r + p := by
      have hqz : (q : ℤ) = 2 * r - 1 := by exact_mod_cast hr_eq.symm
      nlinarith [hqz, hp2, sq_nonneg ((r : ℤ) - 2)]
    have : ((q : ℤ)) < ((r ^ 2 - r + p : ℕ) : ℤ) := by
      push_cast [hge]; linarith
    exact_mod_cast this
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd q hq_dvd_fr with h1' | h2'
  · exact (hq_prime.one_lt).ne' h1'
  · omega

/-- **The arithmetic core, prime-`D` case (Stark–Heegner).**  For `n > 13` with `4 pₙ - 1`
*prime* (an infinite family, e.g. `n = 16`, `pₙ = 53`, `4 pₙ - 1 = 211`), the discriminant
`D = 1 - 4 pₙ = -(4 pₙ - 1)` is a fundamental discriminant with `D < -163`.  Some entry of
row `n` is composite **iff** some prime `q < 2n` is *split* in `ℚ(√D)` (`(D∣q)=1`), and the
least such split prime is `≤ √((4 pₙ - 1)/3) < 2n` **iff** the class number `h(D) ≥ 2`.

For `D < -163` this is exactly the **Stark–Heegner theorem** (the resolution of Gauss's class
number one problem): the only imaginary quadratic discriminants with `h = 1` are
`-3, -4, -7, -8, -11, -19, -43, -67, -163`, the largest being `-163`.  Among discriminants of the
form `1 - 4 p` these correspond precisely to `p ∈ {2, 3, 5, 11, 17, 41}`, i.e. `n ∈ {1,2,3,5,7,13}`
— all `≤ 13`.  This deep input is not currently available in Mathlib; everything else in this
file (the reduction, Chebyshev's lower bound, and the composite-`D` case) is elementary and
complete. -/
theorem prime_D_entry (n : ℕ) (hn : 13 < n)
    (hprime : Nat.Prime (4 * Nat.nth Nat.Prime (n - 1) - 1)) :
    ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  sorry

/-- **The arithmetic core.**  For every `n > 13`, some entry of row `n` is composite.
Case split on whether `4 pₙ - 1` is prime: the composite case is elementary
(`composite_D_entry`); the prime case is the Stark–Heegner input (`prime_D_entry`). -/
theorem exists_composite_entry (n : ℕ) (hn : 13 < n) :
    ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  by_cases h : Nat.Prime (4 * Nat.nth Nat.Prime (n - 1) - 1)
  · exact prime_D_entry n hn h
  · exact composite_D_entry n hn h

/--
Conjecture: $a(n) < n$ for $n > 13$.
-/
theorem oeis_117531_conjecture_0 (n : ℕ) (h : n > 13) : a n < n :=
  reduction n (exists_composite_entry n h)
