import FormalConjectures.Util.ProblemImports

open Nat

/--
The auxiliary sequence $x(n)$, where $x(1)=1$ and $x(n) = 2 \cdot x(n-1) + \mathrm{lcm}(x(n-1), n)$ for $n > 1$.
`x_seq n` corresponds to the OEIS term $x(n)$.
This definition is set up for `n : ℕ` where $n=0$ and $n=1$ are base cases for $x(0)$ and $x(1)$.
Note: Mathlib's `lcm` is `Nat.lcm`.
-/
def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

/--
A135508: $a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2*x(n-1) + \operatorname{lcm}(x(n-1),n)$.
-/
def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- We rely on the fact that x_seq n divides x_seq (n+1), which is a known property of the sequence.
    -- Since n : ℕ, the division is integer division.
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n

    -- The fact that x_seq n divides x_seq (n+1) means that the division is exact.
    -- The final result is always a natural number.
    (x_n_plus_1 / x_n) - 2


lemma x_seq_succ_succ (n : ℕ) :
    x_seq (n + 2) = 2 * x_seq (n + 1) + Nat.lcm (x_seq (n + 1)) (n + 2) := by
  rfl

lemma x_seq_pos (n : ℕ) (hn : 1 ≤ n) : 0 < x_seq n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [x_seq]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [x_seq_succ_succ]
      have := ih hk
      positivity

/-- The multiplicative form of the recurrence: `x(n+1) = x(n) * (2 + (n+1)/gcd(x(n), n+1))`. -/
lemma x_seq_succ_eq (n : ℕ) (hn : 1 ≤ n) :
    x_seq (n + 1) = x_seq n * (2 + (n + 1) / Nat.gcd (x_seq n) (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [x_seq_succ_succ]
  have hpos : 0 < x_seq (k + 1) := x_seq_pos _ (by omega)
  have hg : 0 < Nat.gcd (x_seq (k + 1)) (k + 1 + 1) := Nat.gcd_pos_of_pos_left _ hpos
  have hlcm : Nat.lcm (x_seq (k + 1)) (k + 1 + 1) =
      x_seq (k + 1) * ((k + 1 + 1) / Nat.gcd (x_seq (k + 1)) (k + 1 + 1)) := by
    rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
  rw [hlcm]; ring

lemma A135508_eq (n : ℕ) (hn : 1 ≤ n) :
    A135508 n = (n + 1) / Nat.gcd (x_seq n) (n + 1) := by
  have hpos : 0 < x_seq n := x_seq_pos n hn
  simp only [A135508, if_neg (by omega : n ≠ 0)]
  rw [x_seq_succ_eq n hn, Nat.mul_div_cancel_left _ hpos]
  simp

/-- For a prime `p`, the conjecture at `p` says exactly that `p ∤ x(p-1)`. -/
lemma conj_iff_not_dvd (p : ℕ) (hp : p.Prime) :
    A135508 (p - 1) = p ↔ ¬ p ∣ x_seq (p - 1) := by
  have h2 := hp.two_le
  rw [A135508_eq (p - 1) (by omega), show p - 1 + 1 = p by omega]
  constructor
  · intro h hd
    have : Nat.gcd (x_seq (p - 1)) p = p := Nat.gcd_eq_right hd
    rw [this, Nat.div_self hp.pos] at h
    omega
  · intro hd
    have hc : Nat.Coprime (x_seq (p - 1)) p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]; exact hd
    rw [hc, Nat.div_one]

/-- `x(n)` divides `x(m)` for `1 ≤ n ≤ m`. -/
lemma x_seq_dvd (n m : ℕ) (hn : 1 ≤ n) (h : n ≤ m) : x_seq n ∣ x_seq m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k n with hk | hk
    · have : n = k + 1 := by omega
      subst this; exact dvd_rfl
    · exact (ih hk).trans (Dvd.intro _ (x_seq_succ_eq k (by omega)).symm)

/-- If a prime `q` divides `x(n)` (with `n ≥ 1`), then `q` divides `2 + (m+1)/gcd(x(m), m+1)`
for some `1 ≤ m < n`. -/
lemma prime_dvd_x_seq (q n : ℕ) (hq : q.Prime) (hn : 1 ≤ n) (h : q ∣ x_seq n) :
    ∃ m, 1 ≤ m ∧ m < n ∧ q ∣ 2 + (m + 1) / Nat.gcd (x_seq m) (m + 1) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [x_seq] at h; exact absurd h hq.one_lt.ne'
    · rw [x_seq_succ_eq k hk] at h
      rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · obtain ⟨m, hm1, hm2, hm3⟩ := ih hk h
        exact ⟨m, hm1, by omega, hm3⟩
      · exact ⟨k, hk, by omega, h⟩

/-- Reduction: for a prime `p ≥ 5`, `p ∣ x(p-1)` iff `gcd(x(p-3), p-2) = 1`. -/
lemma prime_dvd_x_seq_iff (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    p ∣ x_seq (p - 1) ↔ Nat.Coprime (x_seq (p - 3)) (p - 2) := by
  constructor
  · intro h
    obtain ⟨m, hm1, hm2, hm3⟩ := prime_dvd_x_seq p (p - 1) hp (by omega) h
    -- `2 + (m+1)/g ≤ m + 3 ≤ p + 1` and `≥ 3`, so it equals `p`.
    have hg : 0 < Nat.gcd (x_seq m) (m + 1) := Nat.gcd_pos_of_pos_left _ (x_seq_pos m hm1)
    have hle : (m + 1) / Nat.gcd (x_seq m) (m + 1) ≤ m + 1 := Nat.div_le_self _ _
    have hpos : 0 < (m + 1) / Nat.gcd (x_seq m) (m + 1) :=
      Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hg
    obtain ⟨c, hc⟩ := hm3
    have hc1 : c = 1 := by
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · interval_cases c <;> omega
      · have := Nat.mul_le_mul_left p hc2; omega
    subst hc1
    have hq : (m + 1) / Nat.gcd (x_seq m) (m + 1) = p - 2 := by omega
    have hdvd : (m + 1) / Nat.gcd (x_seq m) (m + 1) ∣ m + 1 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    rw [hq] at hdvd
    have hm : m + 1 = p - 2 := by
      obtain ⟨d, hd⟩ := hdvd
      rcases Nat.lt_or_ge d 2 with hd2 | hd2
      · interval_cases d <;> omega
      · have := Nat.mul_le_mul_left (p - 2) hd2; omega
    have hm' : m = p - 3 := by omega
    subst hm'
    rw [hm] at hq
    -- `(p-2)/gcd = p-2` forces `gcd = 1`
    have hg' : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := by
      have hgpos : 0 < Nat.gcd (x_seq (p - 3)) (p - 2) := by
        rw [hm] at hg; exact hg
      set g := Nat.gcd (x_seq (p - 3)) (p - 2) with hgdef
      have hgd : g ∣ p - 2 := Nat.gcd_dvd_right _ _
      obtain ⟨e, he⟩ := hgd
      have h1 : (p - 2) / g = e := by rw [he]; exact Nat.mul_div_cancel_left _ hgpos
      have h2 : e = p - 2 := by rw [← h1, hq]
      have h3 : g * e = 1 * e := by rw [one_mul, ← he, h2]
      exact Nat.eq_of_mul_eq_mul_right (by omega) h3
    exact hg'
  · intro h
    have h1 : 1 ≤ p - 3 := by omega
    have : x_seq (p - 3 + 1) = x_seq (p - 3) * (2 + (p - 3 + 1) / Nat.gcd (x_seq (p - 3)) (p - 3 + 1)) :=
      x_seq_succ_eq (p - 3) h1
    rw [show p - 3 + 1 = p - 2 by omega, h, Nat.div_one, show 2 + (p - 2) = p by omega] at this
    have hd : p ∣ x_seq (p - 2) := ⟨x_seq (p - 3), by rw [this]; ring⟩
    exact hd.trans (x_seq_dvd (p - 2) (p - 1) (by omega) (by omega))

/-- The conjecture is equivalent to the following statement: for every prime `p ≥ 5`
such that `p - 2` is not prime, `x(p-3)` and `p-2` have a common factor. -/
theorem conj_reformulation :
    (∀ p : ℕ, Nat.Prime p → ¬ Nat.Prime (p - 2) → A135508 (p - 1) = p) ↔
    (∀ p : ℕ, Nat.Prime p → 5 ≤ p → ¬ Nat.Prime (p - 2) → ¬ Nat.Coprime (x_seq (p - 3)) (p - 2)) := by
  constructor
  · intro H p hp h5 h2 hc
    have := H p hp h2
    rw [conj_iff_not_dvd p hp, prime_dvd_x_seq_iff p hp h5] at this
    exact this hc
  · intro H p hp h2
    rw [conj_iff_not_dvd p hp]
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · have := hp.two_le
      interval_cases p
      · decide
      · decide
      · exact absurd (by decide : Nat.Prime 2) h2
    · rw [prime_dvd_x_seq_iff p hp h5]; exact H p hp h5 h2

/-- A prime `r` is *good* if `r - 2` is not prime, or `r = 7`. For such `r` (and only such `r`,
inductively) one has `A135508 (r-1) = r`, i.e. `x(r) = x(r-1) * (r + 2)`. -/
def GoodPrime (r : ℕ) : Prop := r.Prime ∧ (r = 7 ∨ ¬ (r - 2).Prime)

/-- The number-theoretic hypothesis to which the conjecture reduces: for every prime `p ≥ 5`
with `p - 2` composite, some prime factor `q` of `p - 2` divides `r + 2` for a good prime
`r < p - 2` (equivalently, `r ≡ -2 (mod q)`). This is a least-prime-in-arithmetic-progression
statement with exponent `2`, currently far out of reach (Linnik's exponent is `5`). -/
def PrimeInAPHypothesis : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ (p - 2).Prime →
    ∃ q r : ℕ, q.Prime ∧ q ∣ p - 2 ∧ r < p - 2 ∧ GoodPrime r ∧ q ∣ r + 2

lemma x_seq_seven : x_seq 7 = 4860 := by decide
lemma x_seq_two : x_seq 2 = 4 := by decide

/-- **Conditional proof of the conjecture.** Assuming `PrimeInAPHypothesis`, the conjecture holds. -/
theorem conjecture_of_PrimeInAPHypothesis (H : PrimeInAPHypothesis) :
    ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro hp h2
  rw [conj_iff_not_dvd p hp]
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · have := hp.two_le
    interval_cases p
    · decide
    · decide
    · exact absurd (by decide : Nat.Prime 2) h2
  rw [prime_dvd_x_seq_iff p hp h5]
  intro hcop
  obtain ⟨q, r, hq, hqN, hrN, hr, hqr⟩ := H p hp h5 h2
  -- `q ∣ x(r)`: since `r` is good, `x(r) = x(r-1) * (r + 2)`.
  have hr2 := hr.1.two_le
  have hxr : (r + 2) ∣ x_seq r := by
    rcases hr.2 with h7 | hgood
    · subst h7; rw [x_seq_seven]; decide
    · have hb : ¬ r ∣ x_seq (r - 1) := by
        have := ih r (by omega) hr.1 hgood
        rwa [conj_iff_not_dvd r hr.1] at this
      have hc : Nat.Coprime (x_seq (r - 1)) r := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr.1]; exact hb
      have := x_seq_succ_eq (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega, hc, Nat.div_one] at this
      exact ⟨x_seq (r - 1), by rw [this]; ring⟩
  have hq1 : q ∣ x_seq (p - 3) :=
    (hqr.trans hxr).trans (x_seq_dvd r (p - 3) (by omega) (by omega))
  have : q ∣ Nat.gcd (x_seq (p - 3)) (p - 2) := Nat.dvd_gcd hq1 hqN
  rw [hcop] at this
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

/-!
## Status of the conjecture (analysis)

Write `b(m) = A135508 (m-1) = m / gcd(x(m-1), m)` and `c(m) = 2 + b(m)`, so that
`x(n) = ∏_{m=2}^{n} c(m)`.  The lemmas below show, purely elementarily, that for a prime `p ≥ 5`

  `A135508 (p-1) = p  ↔  ¬ p ∣ x(p-1)  ↔  gcd(x(p-3), p-2) > 1`,

so the conjecture is equivalent to: *for every prime `p ≥ 5` with `N = p - 2` composite, some
prime factor `q` of `N` divides `x(N-1)`* (`conj_reformulation`).

By induction the primes dividing `x(n)` are exactly `2, 3, 5` and the prime factors of `r + 2`
for the primes `r ≤ n` with `r - 2` not prime (for such `r` we have `b(r) = r`, `c(r) = r + 2`).
Hence the conjecture is equivalent to a statement about *least primes in arithmetic
progressions*: for every prime `p` with `N = p - 2` composite, some prime factor `q ∣ N`
admits a prime `r < N`, `r ≡ -2 (mod q)`, with `r - 2` composite.  Taking `N = q·q'` with
`q' ≈ q`, this needs a prime `≡ -2 (mod q)` below roughly `q²`, i.e. Linnik's theorem with
exponent `2` — far beyond what is provable (the best known exponent is `5`).  Numerically the
conjecture holds for all `p ≤ 3·10⁷`, and heuristically no counterexample exists.
Neither theorem below can therefore be completed with current mathematics.
-/

/--
Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p.
p-2 in natural numbers is $\max(0, p-2)$.
A prime $p$ such that $p-2$ is not a prime means $p$ is not the larger element of a twin prime pair, except for $p=3$ where $p-2=1$ (not prime) and $p=2$ where $p-2=0$ (not prime).
-/
theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  sorry

theorem oeis_135508_conjecture_0.disproof : ¬ (type_of% @oeis_135508_conjecture_0) := sorry
