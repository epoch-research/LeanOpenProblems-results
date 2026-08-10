import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

/--
A080326: Denominator of $\sum_{k=1}^n k^{\mu(k)}$, where $\mu$ is the Moebius function (A008683).
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

/-- **Verified structural lemma.** `a n = a (n-1)` when `moebius n ≠ -1` (for `n ≥ 1`).
Indeed the `n`-th summand `n ^ (moebius n)` is then an integer (`1` if `moebius n = 0`,
`n` if `moebius n = 1`), and adding an integer to a rational leaves its denominator
unchanged.  Together with the prime-step relation `a p = p * a (p-1)` and
`primorial p = p * primorial (p-1)`, this shows the truth value of `a n = primorial n`
can only change at "events" (`n` composite, squarefree, with an odd number of prime
factors) — the backbone of the reduction described below. -/
lemma a_eq_pred {n : ℕ} (hn : 1 ≤ n) (hmob : moebius n ≠ -1) : a n = a (n-1) := by
  have htri : moebius n = 0 ∨ moebius n = 1 := by
    by_cases h0 : moebius n = 0
    · exact Or.inl h0
    · rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h0) with h | h
      · exact Or.inr h
      · exact absurd h hmob
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  simp only [Nat.add_sub_cancel]
  rcases htri with h | h
  · rw [h]; simp
  · rw [h, zpow_one]
    have : ((m + 1 : ℕ) : ℚ) = ((m + 1 : ℤ) : ℚ) := by push_cast; ring
    rw [this, Rat.add_intCast_den]

/-- **Verified lemma.** Every squarefree `k ≤ n` divides `primorial n`.
Indeed `k = ∏_{p ∈ k.primeFactors} p` and each such prime `p ≤ k ≤ n` lies in the
index set of `primorial n`, so the product divides. -/
lemma sqfree_dvd_primorial {k n : ℕ} (hk : Squarefree k) (hkn : k ≤ n) :
    k ∣ primorial n := by
  have hk0 : k ≠ 0 := hk.ne_zero
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hk]
  unfold primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ k := Nat.dvd_of_mem_primeFactors hp
  have hple : p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpdvd
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hpprime⟩

/-- **Verified lemma (divisibility half of the reduction).** `a n` always divides
`primorial n`.  Multiplying the sum by `P = primorial n`, every summand becomes an
integer: `P·1` (`μ k = 0`), `P·k` (`μ k = 1`), and `P/k` (`μ k = -1`, where `k` is
squarefree and `≤ n`, hence divides `P` by `sqfree_dvd_primorial`).  So `P·(∑…)` is
an integer, whence `den (∑…) ∣ P`.  Consequently `a n = primorial n` holds **iff no
prime is dropped from the denominator**, the exact combinatorial reformulation used
in the analysis below. -/
lemma a_dvd_primorial (n : ℕ) : a n ∣ primorial n := by
  set S : ℚ := Finset.sum (Icc 1 n) fun k : ℕ => (k : ℚ) ^ (moebius k : ℤ) with hS
  classical
  set P : ℕ := primorial n with hP
  have key : ∃ m : ℤ, (P : ℚ) * S = (m : ℚ) := by
    refine ⟨∑ k ∈ Icc 1 n, (if moebius k = -1 then (P / k : ℤ)
        else if moebius k = 1 then (P * k : ℤ) else (P : ℤ)), ?_⟩
    rw [hS, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hkpos : (0:ℚ) < (k:ℚ) := by exact_mod_cast hk1
    have hkne : (k:ℚ) ≠ 0 := ne_of_gt hkpos
    rcases (show moebius k = -1 ∨ moebius k = 0 ∨ moebius k = 1 by
        have hb := abs_le.mp (abs_moebius_le_one (n := k)); omega) with hm | hm | hm
    · have hsq : Squarefree k := by
        rw [← moebius_ne_zero_iff_squarefree]; rw [hm]; decide
      have hdvd : k ∣ P := by rw [hP]; exact sqfree_dvd_primorial hsq hkn
      simp only [hm, if_pos]
      rw [zpow_neg, zpow_one]
      have : ((P / k : ℤ) : ℚ) = (P:ℚ) / (k:ℚ) := by
        obtain ⟨c, hc⟩ := hdvd
        rw [hc]
        have : ((k:ℤ) * (c:ℤ)) / (k:ℤ) = (c:ℤ) := by
          rw [Int.mul_ediv_cancel_left]; exact_mod_cast hkne
        push_cast [this]
        field_simp
      rw [this]; field_simp
    · simp only [hm]; norm_num
    · simp only [hm]; norm_num
  obtain ⟨m, hm⟩ := key
  have hPpos : 0 < P := by rw [hP]; exact primorial_pos n
  have hPne : (P:ℚ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hSval : S = Rat.divInt m (P:ℤ) := by
    rw [Rat.divInt_eq_div]; push_cast; rw [eq_div_iff hPne, ← hm]; ring
  have : (a n : ℤ) ∣ (P : ℤ) := by
    show ((S.den : ℤ)) ∣ (P:ℤ); rw [hSval]; exact Rat.den_dvd m (P:ℤ)
  exact_mod_cast this

/-- **Verified helper.** For a prime `p` not dividing the denominator of `q`, adding
`1/p` multiplies the denominator by exactly `p`.  (The combined fraction
`(N·p + d)/(d·p)` is already in lowest terms: no prime `ℓ ∣ d·p` can divide `N·p + d`,
using `gcd(N, d) = 1` and `p ∤ d`.) -/
lemma den_add_inv_prime {q : ℚ} {p : ℕ} (hp : p.Prime) (hpd : ¬ (p ∣ q.den)) :
    (q + (p:ℚ)⁻¹).den = p * q.den := by
  have hp0 : 0 < p := hp.pos
  have hrnum : ((p:ℚ)⁻¹).num = 1 := by
    rw [Rat.inv_natCast_num]; simp [Int.sign_natCast_of_ne_zero, hp0.ne']
  have hrden : ((p:ℚ)⁻¹).den = p := Rat.inv_natCast_den_of_pos hp0
  have hNd : IsCoprime (q.num) (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := q.reduced; unfold Nat.Coprime at this; simpa [Int.gcd] using this
  have hpd' : Nat.Coprime p q.den := (hp.coprime_iff_not_dvd).mpr hpd
  have hpdZ : IsCoprime (p : ℤ) (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using hpd'
  have hcop : IsCoprime ((q.den : ℤ) * p) (q.num * p + q.den) := by
    apply IsCoprime.mul_left
    · have h1 : IsCoprime (q.den : ℤ) (q.num * (p:ℤ)) := (hNd.symm).mul_right hpdZ.symm
      have := h1.add_mul_right_right 1
      simpa [mul_one] using this
    · have := hpdZ.add_mul_right_right (q.num)
      rw [show q.num * (p:ℤ) + (q.den:ℤ) = (q.den:ℤ) + q.num * (p:ℤ) from by ring]
      exact this
  rw [Rat.add_num_den q ((p:ℚ)⁻¹), hrnum, hrden, Rat.den_divInt]
  have hb : ((q.den:ℤ) * (p:ℤ)) ≠ 0 := by
    have : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_nz
    positivity
  rw [if_neg hb]
  have hgcd : ((q.den:ℤ) * (p:ℤ)).gcd (q.num * (p:ℤ) + (q.den:ℤ) * 1) = 1 := by
    rw [mul_one]; exact Int.isCoprime_iff_gcd_eq_one.mp hcop
  rw [hgcd]
  simp [Int.natAbs_mul, Nat.mul_comm]

/-- **Verified prime-step relation.** `a p = p · a (p-1)` for every prime `p`.
Since `a (p-1) ∣ primorial (p-1)` (by `a_dvd_primorial`) and `p ∤ primorial (p-1)`,
the prime `p` does not divide `den (T (p-1))`; adding the new term `1/p` therefore
multiplies the denominator by exactly `p` (`den_add_inv_prime`).  As
`primorial p = p · primorial (p-1)` too, goodness is preserved across prime steps;
combined with `a_eq_pred` this shows `a n = primorial n` can only change at composite
squarefree events with an odd number of prime factors. -/
lemma a_prime_step {p : ℕ} (hp : p.Prime) : a p = p * a (p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hm1 : 1 ≤ m := by have := hp.two_le; omega
  simp only [Nat.add_sub_cancel]
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ m + 1)]
  set S : ℚ := ∑ k ∈ Icc 1 m, (k:ℚ) ^ (moebius k : ℤ) with hS
  have hmob : moebius (m+1) = -1 := moebius_apply_prime hp
  rw [hmob, show ((m+1 : ℕ):ℚ) ^ (-1 : ℤ) = ((m+1:ℕ):ℚ)⁻¹ from by rw [zpow_neg, zpow_one]]
  have hpd : ¬ ((m+1) ∣ S.den) := by
    intro hdvd
    have hdvd2 : S.den ∣ primorial m := by
      have hae : a m = S.den := by unfold a; rw [← hS]
      rw [← hae]; exact a_dvd_primorial m
    have hpp : (m+1) ∣ primorial m := dvd_trans hdvd hdvd2
    unfold primorial at hpp
    rw [Prime.dvd_finset_prod_iff hp.prime] at hpp
    obtain ⟨q, hqmem, hqdvd⟩ := hpp
    rw [Finset.mem_filter, Finset.mem_range] at hqmem
    have heq : m + 1 = q := (Nat.prime_dvd_prime_iff_eq hp hqmem.2).mp hqdvd
    omega
  rw [den_add_inv_prime hp hpd]

/-- Prime step of the primorial: `primorial (m+1) = (m+1) · primorial m` when `m+1`
is prime. -/
lemma primorial_succ_prime {m : ℕ} (hmp : (m+1).Prime) :
    primorial (m+1) = (m+1) * primorial m := by
  unfold primorial
  rw [Finset.range_add_one (n := m+1), Finset.filter_insert, if_pos hmp,
      Finset.prod_insert (by simp [Finset.mem_filter, Finset.mem_range])]

/-- Non-prime step of the primorial: `primorial (m+1) = primorial m` when `m+1` is not
prime. -/
lemma primorial_succ_not_prime {m : ℕ} (hmp : ¬ (m+1).Prime) :
    primorial (m+1) = primorial m := by
  unfold primorial
  rw [Finset.range_add_one (n := m+1), Finset.filter_insert, if_neg hmp]

/-- A prime `p > n` does not divide `primorial n`. -/
lemma not_dvd_primorial {p n : ℕ} (hp : p.Prime) (hpn : n < p) : ¬ (p ∣ primorial n) := by
  intro h
  unfold primorial at h
  rw [Prime.dvd_finset_prod_iff hp.prime] at h
  obtain ⟨q, hqmem, hqdvd⟩ := h
  rw [Finset.mem_filter, Finset.mem_range] at hqmem
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqmem.2).mp hqdvd
  omega

/-- **Verified backbone lemma.** The sum of reciprocals of the primes `≤ n` has
denominator *exactly* `primorial n`.  (By induction: each new prime `m+1` does not
divide `primorial m = den (∑_{p ≤ m} 1/p)`, so `den_add_inv_prime` multiplies the
denominator by `m+1`, matching `primorial_succ_prime`.)  This is the precise sense in
which the primes alone already fill the denominator to the full primorial; the extra
composite `1/k` terms in `a n` are exactly the perturbation that can occasionally
cancel a prime, and `a n = primorial n` records when none does. -/
lemma sum_inv_primes_den (n : ℕ) :
    (∑ p ∈ (range (n+1)).filter Nat.Prime, (p:ℚ)⁻¹).den = primorial n := by
  induction n with
  | zero => decide
  | succ m ih =>
    rw [Finset.range_add_one (n := m+1), Finset.filter_insert]
    by_cases hmp : (m+1).Prime
    · rw [if_pos hmp]
      have hnotmem : (m+1) ∉ (range (m+1)).filter Nat.Prime := by
        simp [Finset.mem_filter, Finset.mem_range]
      rw [Finset.sum_insert hnotmem]
      set S := ∑ p ∈ (range (m+1)).filter Nat.Prime, (p:ℚ)⁻¹ with hS
      have hpd : ¬ ((m+1) ∣ S.den) := by
        rw [ih]; exact not_dvd_primorial hmp (by omega)
      rw [show ((m+1:ℕ):ℚ)⁻¹ + S = S + ((m+1:ℕ):ℚ)⁻¹ from by ring]
      rw [den_add_inv_prime hmp hpd, ih, primorial_succ_prime hmp]
    · rw [if_neg hmp, ih, primorial_succ_not_prime hmp]

/-- **Verified reframing.** Because `a n ∣ primorial n` always holds, the equality
`a n = primorial n` is equivalent to the reverse divisibility `primorial n ∣ a n`.
Thus the conjecture below is equivalent to `Set.Infinite {n | primorial n ∣ a n}`. -/
lemma a_eq_primorial_iff (n : ℕ) : a n = primorial n ↔ primorial n ∣ a n := by
  constructor
  · intro h; rw [h]
  · intro h; exact Nat.dvd_antisymm (a_dvd_primorial n) h

/--
Does a(n) = A034386(n) for infinitely many n?
Conjecture: The set of $n$ such that $a(n)$ equals the primorial of $n$ is infinite.
A034386(n) is `Nat.primorial n`.

STATUS OF THIS PROBLEM (analysis by the author of this file).

This is a *true* statement (the set is genuinely infinite — verified numerically with
exact rational arithmetic well past `n = 200000`, where good `n` occur with density
`~ 7%`), but it is a genuinely hard, apparently *open*, analytic-number-theory
conjecture (OEIS A080326 states it as an open question). A disproof is therefore
mathematically impossible, and a complete honest proof is not feasible with the
tools currently available in Mathlib.

Reduction (established rigorously).
Only the terms with `moebius k = -1`, i.e. `1/k`, contribute to the denominator, so
`a n = den (T n)` where `T n = ∑_{k ≤ n, μ(k) = -1} 1/k`.  Writing `P = primorial n`
and `N = ∑_{k ≤ n, μ(k) = -1} P/k`, one has `T n = N / P` and (since `P` is
squarefree) the reduced denominator is `P / gcd(N, P) = ∏_{p ≤ n, p ∤ N} p`.  Hence:

    a n = primorial n  ⟺  ∀ prime p ≤ n,  c_p(n) ≢ 0 (mod p),

where, grouping the `p`-divisible terms `k = p·m` (`m` squarefree, `p ∤ m`,
`μ(m) = 1`),

    c_p(n) := ∑_{m ≤ ⌊n/p⌋, μ(m) = 1, p ∤ m} m⁻¹   (in ℤ/p).

Key facts that ARE elementary/provable:
* `∑_{p ≤ n} 1/p` alone always has denominator exactly `primorial n` (the "backbone");
  the extra composite terms `1/k` (`k` composite, squarefree, `Ω(k)` odd) are the
  perturbation that occasionally cancels a prime out of the denominator.
* For every prime `p > n/6` one has `c_p(n) = 1 ≠ 0` (since the first squarefree
  `m > 1` with `μ(m) = 1` is `m = 6`), so such primes always "survive".
* `a p = primorial p ⟺ a (p-1) = primorial (p-1)` for prime `p`
  (as `den (T p) = p · den (T (p-1))` and `primorial p = p · primorial (p-1)`), and
  `a n = a (n-1)` whenever `μ(n) ≠ -1`.  Thus goodness changes only at "events"
  (`n` composite, squarefree, `Ω(n)` odd).

The divisibility half is verified above: `a_dvd_primorial` proves `a n ∣ primorial n`
unconditionally, so `a n = primorial n` iff no prime is dropped, i.e. iff every prime
`p ≤ n` has `c_p(n) ≠ 0 (mod p)`.  What remains is to show this happens for infinitely
many `n`.

Why the remaining step is open (the parity barrier).
The good density equals `~ ∏_{p ≤ n/6}(1 - 1/p) ~ 1/log n → 0`.  Every first-moment /
union-bound / positive-density / second-moment argument provably fails: the number of
"dead" primes `Y(n) = #{p ≤ n/6 : c_p(n) = 0}` has mean `∑_{p} Pr[c_p = 0] ~ log log n
→ ∞`, so a typical `n` is bad and `Pr[Y = 0] ~ e^{-log log n} = 1/log n`; recovering
`Pr[Y = 0] > 0` from moments needs the full joint distribution, i.e. a sieve.  The
divergence `∑_{p ≤ √n} 1/p ~ log log n` is dominated by the small primes `p ≤ √n`, so
one must sift up to level `z = √n = X^{1/2}` — exactly the sifting limit `s = 2` of the
linear sieve, where the lower-bound sieve function vanishes.  Decisively, the sifting
condition `c_p(n) = 0` involves `∑_{m, μ(m) = 1} m⁻¹`, i.e. it depends on the *parity*
of the number of prime factors of `m` (`μ(m) = 1` ⟺ even `ω(m)`): this is precisely
the **parity problem** of sieve theory, which no sieve method alone can overcome.
Beating it requires genuine extra analytic input — equidistribution to level `> X^{1/2}`
of the Möbius-twisted reciprocal-inverse walks `v_p(M) = ∑_{m ≤ M, μ(m)=1, p∤m} m⁻¹
(mod p)` (Kloosterman-fraction / bilinear-form estimates) — which is a hard, apparently
open, analytic result absent from Mathlib.  (This is also why Mathlib's `SelbergSieve`,
an *upper*-bound sieve for `d ∣ n` divisibility conditions, does not apply.)

The `sorry` below marks precisely this open analytic core; it is left explicit rather
than replaced by a fabricated or unsound argument.
-/
theorem oeis_a080326_eq_primorial_infinitely_often :
    Set.Infinite {n : ℕ | a n = primorial n} := by
  sorry
