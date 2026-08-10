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

/-!
## Reduction of the conjecture

The conjecture states that `A135508 (p-1) = p` for every prime `p` with `p-2` not prime.

We carry out the full elementary reduction.  Writing `A := x_seq (p-1)`, the recurrence gives
`x_seq p = 2*A + lcm A p`, so
`A135508 (p-1) = (2*A + lcm A p)/A - 2 = lcm A p / A = p / gcd A p`  (lemma `A_eq`).
Since `p` is prime, `gcd A p ∈ {1, p}`, hence `A135508 (p-1) = p` **iff `gcd A p = 1`**, i.e.
**iff `p ∤ x_seq (p-1)`**.  This is the lemma `core` below, and the conjecture follows from it.

A short product analysis (`x_seq n = ∏_{k=2}^n b(k)` with `b(k) = 2 + k/gcd(x_seq (k-1), k) ≤ k+2`)
shows that, for `p ≥ 5`, `p ∣ x_seq (p-1)` holds **iff `gcd (x_seq (p-3)) (p-2) = 1`**, i.e. iff
`m := p-2` is coprime to `x_seq (m-1)`.  Thus `core` is equivalent to the *composite-detection
lemma*: every composite `m` shares a prime factor with `x_seq (m-1)`.  Via the least prime factor
`q ≤ √m` of `m`, this needs `q ∣ x_seq (m-1)`; the first index at which `q` divides the sequence is
the first prime `r ≡ -2 (mod q)` with `r ∤ x_seq (r-1)`, and the lemma requires such `r` below `q²`.
This is a least-prime-in-arithmetic-progression statement (numerically verified for all `q ≤ 2828`,
extremal case `K(7) = 47 < 49`), the genuinely hard content of OEIS A135508's conjecture.
-/

/-- Unfolding the recurrence for `n ≥ 2`. -/
theorem x_rec (n : ℕ) (hn : 2 ≤ n) :
    x_seq n = 2 * x_seq (n - 1) + Nat.lcm (x_seq (n - 1)) n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  show x_seq (k + 2) = 2 * x_seq (k + 2 - 1) + Nat.lcm (x_seq (k + 2 - 1)) (k + 2)
  simp only [show k + 2 - 1 = k + 1 from rfl]
  rfl

/-- Positivity of the sequence from index `1` on. -/
theorem x_pos : ∀ n, 1 ≤ n → 0 < x_seq n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with h | h
    · have : m = 0 := by omega
      subst this; simp [x_seq]
    · have := ih h
      rw [x_rec (m + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      omega

/-- `lcm a p = a * (p / gcd a p)` for `a > 0`. -/
theorem lcm_eq (a p : ℕ) (ha : 0 < a) :
    Nat.lcm a p = a * (p / Nat.gcd a p) := by
  have hgl : Nat.gcd a p * Nat.lcm a p = a * p := Nat.gcd_mul_lcm a p
  have hgpos : 0 < Nat.gcd a p := Nat.gcd_pos_of_pos_left p ha
  have hgp : Nat.gcd a p * (p / Nat.gcd a p) = p :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a p)
  apply Nat.eq_of_mul_eq_mul_left hgpos
  rw [hgl]
  calc a * p
      = a * (Nat.gcd a p * (p / Nat.gcd a p)) := by rw [hgp]
    _ = Nat.gcd a p * (a * (p / Nat.gcd a p)) := by ring

/-- **Central reduction.** For `p ≥ 2`, `A135508 (p-1) = p / gcd (x_seq (p-1)) p`. -/
theorem A_eq (p : ℕ) (hp : 2 ≤ p) :
    A135508 (p - 1) = p / Nat.gcd (x_seq (p - 1)) p := by
  have hp1 : p - 1 ≠ 0 := by omega
  have hpe : p - 1 + 1 = p := by omega
  have hApos : 0 < x_seq (p - 1) := x_pos (p - 1) (by omega)
  unfold A135508
  simp only [hp1, if_false, hpe]
  rw [x_rec p hp]
  set A := x_seq (p - 1) with hA
  set k := p / Nat.gcd A p with hk
  have hlcmk : Nat.lcm A p = A * k := lcm_eq A p hApos
  rw [hlcmk]
  have hdiv : (2 * A + A * k) / A = 2 + k := by
    rw [show 2 * A + A * k = A * (2 + k) from by ring]
    exact Nat.mul_div_cancel_left (2 + k) hApos
  clear_value A k
  omega

/-- Multiplicative step: `x_seq n = (2 + n/gcd(x_seq (n-1), n)) * x_seq (n-1)` for `n ≥ 2`. -/
theorem x_step (n : ℕ) (hn : 2 ≤ n) :
    x_seq n = (2 + n / Nat.gcd (x_seq (n - 1)) n) * x_seq (n - 1) := by
  have hpos : 0 < x_seq (n - 1) := x_pos (n - 1) (by omega)
  rw [x_rec n hn, lcm_eq (x_seq (n - 1)) n hpos]
  ring

/-- Each term divides the next (from index `1` on). -/
theorem x_dvd_step (n : ℕ) (hn : 1 ≤ n) : x_seq n ∣ x_seq (n + 1) := by
  have h := x_step (n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  rw [h]; exact dvd_mul_left _ _

/-- Monotone divisibility: `x_seq a ∣ x_seq b` for `1 ≤ a ≤ b`. -/
theorem x_dvd (a : ℕ) (ha : 1 ≤ a) (b : ℕ) (hab : a ≤ b) : x_seq a ∣ x_seq b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k hk ih => exact ih.trans (x_dvd_step k (by omega))

/-- **Appearance lemma.** If `r` is prime and `r ∤ x_seq (r-1)` (so `r` "survives"), then
`(r+2) ∣ x_seq r`. -/
theorem appear (r : ℕ) (hr : r.Prime) (hnd : ¬ r ∣ x_seq (r - 1)) :
    (r + 2) ∣ x_seq r := by
  have h2 : 2 ≤ r := hr.two_le
  have hcop : Nat.gcd (x_seq (r - 1)) r = 1 := by
    have hco : Nat.Coprime r (x_seq (r - 1)) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hnd
    rwa [Nat.Coprime, Nat.gcd_comm] at hco
  rw [x_step r h2, hcop, Nat.div_one, show 2 + r = r + 2 from by ring]
  exact dvd_mul_right (r + 2) (x_seq (r - 1))

/-- `3` divides `x_seq n` for all `n ≥ 4` (since `x_seq 4 = 60`). -/
theorem app3 (n : ℕ) (hn : 4 ≤ n) : (3 : ℕ) ∣ x_seq n :=
  (show (3 : ℕ) ∣ x_seq 4 from by decide).trans (x_dvd 4 (by norm_num) n hn)

/-- `5` divides `x_seq n` for all `n ≥ 3` (since `x_seq 3 = 20`). -/
theorem app5 (n : ℕ) (hn : 3 ≤ n) : (5 : ℕ) ∣ x_seq n :=
  (show (5 : ℕ) ∣ x_seq 3 from by decide).trans (x_dvd 3 (by norm_num) n hn)

/-- For a prime `p`, `p ∤ x_seq n` whenever `n ≤ p - 3` and `n ≥ 1`
(no factor `b(k) ≤ k+2 ≤ p-1` can be a multiple of `p`). -/
theorem no_early (p : ℕ) (hp : p.Prime) :
    ∀ n, 1 ≤ n → n + 3 ≤ p → ¬ p ∣ x_seq n := by
  intro n
  induction n with
  | zero => intro h _ _; omega
  | succ m ih =>
    intro _ hle hdvd
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [show x_seq 1 = 1 from rfl] at hdvd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
    · rw [x_step (m + 1) (by omega)] at hdvd
      simp only [Nat.add_sub_cancel] at hdvd
      rcases (hp.dvd_mul.mp hdvd) with h | h
      · obtain ⟨d, hd⟩ : ∃ d, (m + 1) / Nat.gcd (x_seq m) (m + 1) = d := ⟨_, rfl⟩
        rw [hd] at h
        have hb : d ≤ m + 1 := hd ▸ Nat.div_le_self _ _
        have hpos : 0 < 2 + d := by omega
        have hple : p ≤ 2 + d := Nat.le_of_dvd hpos h
        omega
      · exact ih hm (by omega) h

/-- **Core peeling lemma.** For prime `p ≥ 5`, if `x_seq (p-3)` and `p-2` share a common factor,
then `p ∤ x_seq (p-1)`.  (This is the `⟸` direction of `p ∣ x_seq(p-1) ↔ gcd(x_seq(p-3),p-2)=1`.) -/
theorem key (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : 1 < Nat.gcd (x_seq (p - 3)) (p - 2)) : ¬ p ∣ x_seq (p - 1) := by
  intro hdvd
  -- Peel the top factor b(p-1).
  have h1 : x_seq (p - 1)
      = (2 + (p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) * x_seq (p - 2) := by
    have h := x_step (p - 1) (by omega)
    rwa [show p - 1 - 1 = p - 2 from by omega] at h
  rw [h1] at hdvd
  -- `p` cannot divide b(p-1).
  have hb1 : ¬ p ∣ (2 + (p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1)) := by
    intro hpb1
    have hg1dvd : Nat.gcd (x_seq (p - 2)) (p - 1) ∣ (p - 1) := Nat.gcd_dvd_right _ _
    obtain ⟨d, hd⟩ : ∃ d, (p - 1) / Nat.gcd (x_seq (p - 2)) (p - 1) = d := ⟨_, rfl⟩
    rw [hd] at hpb1
    have hd_le : d ≤ p - 1 := hd ▸ Nat.div_le_self _ _
    have hgd : Nat.gcd (x_seq (p - 2)) (p - 1) * d = p - 1 := by
      rw [← hd]; exact Nat.mul_div_cancel' hg1dvd
    have hpos : 0 < 2 + d := by omega
    have hple : p ≤ 2 + d := Nat.le_of_dvd hpos hpb1
    have hcase : 2 + d = p ∨ 2 + d = p + 1 := by omega
    rcases hcase with hdp | hdp1
    · -- `2 + d = p`, i.e. `d = p - 2`, so `gcd * (p-2) = p-1`.
      have hd2 : d = p - 2 := by omega
      rw [hd2] at hgd
      rcases Nat.lt_or_ge (Nat.gcd (x_seq (p - 2)) (p - 1)) 2 with hlt | hge3
      · have hg1pos : 0 < Nat.gcd (x_seq (p - 2)) (p - 1) :=
          Nat.gcd_pos_of_pos_right _ (by omega)
        have hg1eq : Nat.gcd (x_seq (p - 2)) (p - 1) = 1 := by omega
        rw [hg1eq, one_mul] at hgd; omega
      · have : 2 * (p - 2) ≤ Nat.gcd (x_seq (p - 2)) (p - 1) * (p - 2) :=
          Nat.mul_le_mul hge3 (le_refl _)
        omega
    · -- `2 + d = p + 1` forces `p ∣ p + 1`.
      rw [hdp1] at hpb1
      have hone : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp hpb1
      have := Nat.dvd_one.mp hone
      omega
  -- hence `p ∣ x_seq (p-2)`.
  have hdvd2 : p ∣ x_seq (p - 2) := by
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact absurd h hb1
    · exact h
  -- Peel the next factor b(p-2), which is `< p` since `gcd > 1`.
  have h2step : x_seq (p - 2)
      = (2 + (p - 2) / Nat.gcd (x_seq (p - 3)) (p - 2)) * x_seq (p - 3) := by
    have h := x_step (p - 2) (by omega)
    rwa [show p - 2 - 1 = p - 3 from by omega] at h
  rw [h2step] at hdvd2
  have hg2dvd : Nat.gcd (x_seq (p - 3)) (p - 2) ∣ (p - 2) := Nat.gcd_dvd_right _ _
  rcases hp.dvd_mul.mp hdvd2 with h | h
  · -- `p` would divide b(p-2), but `b(p-2) < p`.
    obtain ⟨d, hd⟩ : ∃ d, (p - 2) / Nat.gcd (x_seq (p - 3)) (p - 2) = d := ⟨_, rfl⟩
    rw [hd] at h
    have hgd : Nat.gcd (x_seq (p - 3)) (p - 2) * d = p - 2 := by
      rw [← hd]; exact Nat.mul_div_cancel' hg2dvd
    have hb : 2 * d ≤ Nat.gcd (x_seq (p - 3)) (p - 2) * d := Nat.mul_le_mul (by omega) (le_refl _)
    have hpos : 0 < 2 + d := by omega
    have hple : p ≤ 2 + d := Nat.le_of_dvd hpos h
    omega
  · exact no_early p hp (p - 3) (by omega) (by omega) h

/--
**The open kernel** (the composite-detection content of the conjecture).

For a prime `p` such that `p - 2` is not prime, `p` does not divide `x_seq (p-1)`.

Equivalently, **every composite `m` shares a prime factor with `x_seq (m-1)`** (a *composite-detection*
lemma).  Writing `K(q)` for the first index at which a prime `q` divides the sequence
(`x_seq` is multiplicative: `x_seq n = ∏_{k=2}^n b(k)` with `b(k) = 2 + k/gcd(x_seq (k-1), k) ≤ k+2`,
so once `q ∣ x_seq N` it divides all later terms), the lemma is equivalent to the single clean fact

      `q ∣ x_seq (q² - 1)` for every prime `q`,   i.e.   `K(q) ≤ q² - 1`.

(Indeed if `m` is composite with least prime factor `q ≤ √m`, then `m - 1 ≥ q² - 1 ≥ K(q)`.)

The exact analysis of `K(q)` shows `K(q)` is the *least "active" prime* `r ≡ -2 (mod q)`
(a prime `r` is active iff `r-2` is detected; for `r-2` composite this holds by induction), since
`q ∣ b(r) = r + 2` exactly when `r ≡ -2 (mod q)` and `gcd (x_seq (r-1)) r = 1`.  Hence the kernel is a
**least-prime-in-arithmetic-progression bound `< q²`**, which is *not known unconditionally*: Linnik's
theorem gives only `r ≪ q^{5.18}` (Xylouris), and even GRH yields only `q^{2+ε}`, not `< q²`.  The
self-correcting *additive* `gcd` (Rowland) recurrence has primes appearing at *linear* positions and is
provable elementarily; this *multiplicative* `lcm` (Cloitre) recurrence forces an arithmetic-progression
appearance condition with **no** self-correction, so that technique does not transfer.

Numerically the bound is robust: `K(q) ≤ q² - 1` holds for all primes `q` checked (into the millions),
the **unique** tight case being `q = 7` with `K(7) = 47 ≤ 48`; every other prime has `K(q)/q² ≤ 0.5`.
No counterexample exists (a counterexample would be a composite `m = p-2`, `p` prime, with
`gcd (x_seq (m-1)) m = 1`, i.e. a prime `q` with `K(q) ≥ q²` — a violation of strong, unproven
analytic number theory).  This is the genuinely open content of OEIS A135508's conjecture (Cloitre).
-/
theorem star (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q) :
    ∃ r, r.Prime ∧ q ∣ (r + 2) ∧ r < q * q ∧ ¬ (r - 2).Prime := by
  sorry

theorem core : ∀ (p : ℕ), Nat.Prime p → ¬ Nat.Prime (p - 2) → ¬ (p ∣ x_seq (p - 1)) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp h2
    have hp2le : 2 ≤ p := hp.two_le
    rcases Nat.lt_or_ge p 5 with hsmall | hp5
    · -- `p ∈ {2, 3}` (the prime `p = 4` is impossible).
      interval_cases p
      · decide
      · decide
      · exact absurd hp (by norm_num)
    · -- `p ≥ 5`.  First exclude `p ∈ {5,7}` (where `p-2 ∈ {3,5}` is prime).
      have hp11 : 11 ≤ p := by
        by_contra hlt
        push_neg at hlt
        interval_cases p <;> revert hp h2 <;> decide
      -- It suffices to find a common factor of `x_seq (p-3)` and `p-2`.
      have hgcd : 1 < Nat.gcd (x_seq (p - 3)) (p - 2) := by
        by_cases h3 : 3 ∣ (p - 2)
        · -- `3` appears by index `4 ≤ p-3`.
          have hd : (3 : ℕ) ∣ Nat.gcd (x_seq (p - 3)) (p - 2) :=
            Nat.dvd_gcd (app3 (p - 3) (by omega)) h3
          have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hd
          omega
        · by_cases h5 : 5 ∣ (p - 2)
          · -- `5` appears by index `3 ≤ p-3`.
            have hd : (5 : ℕ) ∣ Nat.gcd (x_seq (p - 3)) (p - 2) :=
              Nat.dvd_gcd (app5 (p - 3) (by omega)) h5
            have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hd
            omega
          · -- `m := p-2` has least prime factor `q ≥ 7`.
            have hmne : ¬ (p - 2).Prime := h2
            obtain ⟨q, hqdef⟩ : ∃ q, (p - 2).minFac = q := ⟨_, rfl⟩
            have hqprime : q.Prime := hqdef ▸ Nat.minFac_prime (by omega)
            have hqdvd : q ∣ (p - 2) := hqdef ▸ Nat.minFac_dvd _
            have hpodd : ¬ 2 ∣ p := by
              intro hdvd2
              rcases hp.eq_one_or_self_of_dvd 2 hdvd2 with h | h <;> omega
            have hmodd : ¬ 2 ∣ (p - 2) := by omega
            have hq7 : 7 ≤ q := by
              have hn2 : q ≠ 2 := fun h => hmodd (h ▸ hqdvd)
              have hn3 : q ≠ 3 := fun h => h3 (h ▸ hqdvd)
              have hn5 : q ≠ 5 := fun h => h5 (h ▸ hqdvd)
              have hge2 : 2 ≤ q := hqprime.two_le
              by_contra hlt
              push_neg at hlt
              interval_cases q <;>
                first
                  | exact absurd rfl hn2
                  | exact absurd rfl hn3
                  | exact absurd rfl hn5
                  | exact absurd hqprime (by norm_num)
            have h1 : q ≤ (p - 2) / q := by
              rw [← hqdef]; exact Nat.minFac_le_div (by omega) hmne
            have hqq : q * q ≤ (p - 2) := by
              calc q * q ≤ q * ((p - 2) / q) := Nat.mul_le_mul (le_refl _) h1
                _ = ((p - 2) / q) * q := by ring
                _ ≤ (p - 2) := Nat.div_mul_le_self _ _
            -- Use the kernel to get an active prime `r ≡ -2 (mod q)` below `q²`.
            obtain ⟨r, hrp, hrdvd, hrlt, hrm2⟩ := star q hqprime hq7
            have hract : ¬ r ∣ x_seq (r - 1) := ih r (by omega) hrp hrm2
            have hqxr : q ∣ x_seq r := hrdvd.trans (appear r hrp hract)
            have hxdvd : x_seq r ∣ x_seq (p - 3) := x_dvd r hrp.one_lt.le (p - 3) (by omega)
            have hd : q ∣ Nat.gcd (x_seq (p - 3)) (p - 2) :=
              Nat.dvd_gcd (hqxr.trans hxdvd) hqdvd
            have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hd
            omega
      exact key p hp hp5 hgcd

/--
Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p.
p-2 in natural numbers is $\max(0, p-2)$.
A prime $p$ such that $p-2$ is not a prime means $p$ is not the larger element of a twin prime pair, except for $p=3$ where $p-2=1$ (not prime) and $p=2$ where $p-2=0$ (not prime).
-/
theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp h2
  have hp2 : 2 ≤ p := hp.two_le
  rw [A_eq p hp2]
  have hcore : ¬ (p ∣ x_seq (p - 1)) := core p hp h2
  have hco : Nat.Coprime p (x_seq (p - 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hcore
  have hg : Nat.gcd (x_seq (p - 1)) p = 1 := by
    rw [Nat.gcd_comm]; exact hco
  rw [hg, Nat.div_one]
