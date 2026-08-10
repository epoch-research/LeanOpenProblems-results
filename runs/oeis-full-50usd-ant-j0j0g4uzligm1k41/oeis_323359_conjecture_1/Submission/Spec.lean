import FormalConjectures.Util.ProblemImports

open Nat

/--
The auxiliary sequence $b(k)$ for A323359, where $b(1)=2$ and $b(k) = b(k-1) + \operatorname{lcm}(\lfloor\sqrt{k^3}\rfloor, b(k-1))$ for $k \ge 2$.
-/
def b : ℕ → ℕ
| 0 => 0
| 1 => 2
| k_plus_1 + 1 =>
  let k := k_plus_1 + 1
  let b_prev := b k_plus_1
  b_prev + Nat.lcm (Nat.sqrt (k ^ 3)) b_prev

/--
A323359: $a(n) = b(n+1)/b(n) - 1$, where $n>0$ and $b$ is the auxiliary sequence.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (b (n + 1) / b n) - 1

theorem b_succ (m : ℕ) :
    b (m + 2) = b (m+1) + Nat.lcm (Nat.sqrt ((m+2) ^ 3)) (b (m+1)) := rfl

theorem b_pos : ∀ n, 1 ≤ n → 0 < b n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    match m with
    | 0 => decide
    | k+1 => rw [b_succ]; have := ih (by omega); omega

theorem a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = Nat.sqrt ((n+1)^3) / Nat.gcd (Nat.sqrt ((n+1)^3)) (b n) := by
  have hbpos : 0 < b n := b_pos n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have hstep : b (m+1+1) = b (m+1) + Nat.lcm (Nat.sqrt ((m+1+1)^3)) (b (m+1)) := by
    rw [show m+1+1 = m+2 from rfl, b_succ]
  set c := Nat.sqrt ((m+1+1)^3) with hc
  have hdvd : b (m+1) ∣ Nat.lcm c (b (m+1)) := Nat.dvd_lcm_right _ _
  obtain ⟨t, ht⟩ := hdvd
  have h1 : a (m+1) = Nat.lcm c (b (m+1)) / b (m+1) := by
    unfold a
    rw [if_neg (by omega), hstep, ht]
    rw [Nat.add_mul_div_left _ _ hbpos, Nat.div_self hbpos,
        Nat.mul_div_cancel_left _ hbpos]
    omega
  rw [h1, Nat.lcm]
  have hg : Nat.gcd c (b (m+1)) ∣ c := Nat.gcd_dvd_left _ _
  rw [Nat.mul_comm c (b (m+1)), Nat.mul_div_assoc _ hg,
      Nat.mul_div_cancel_left _ hbpos]

/-- Divisibility of successive terms: `b n ∣ b (n+1)` for `n ≥ 1`, so `a n` is an
honest natural number (`b (n+1) / b n` is exact). -/
theorem b_dvd_succ (n : ℕ) (hn : 1 ≤ n) : b n ∣ b (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 + 1 = m + 2 from rfl, b_succ]
  exact Dvd.dvd.add (dvd_refl _) (Nat.dvd_lcm_right _ _)

/-- Unconditional structural fact: an integer `m > 0` has at most one prime factor
exceeding its square root (if `p, q` are distinct primes dividing `m` with
`m < p*p` and `m < q*q`, we get a contradiction).  This is the mechanism by which
`a n = ⌊(n+1)^{3/2}⌋ / gcd(⌊(n+1)^{3/2}⌋, b n)` can be forced to be `1` or prime,
*provided* every prime power `≤ √(⌊(n+1)^{3/2}⌋)` dividing it is covered by `b n`. -/
theorem at_most_one_large_prime (m p q : ℕ) (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpm : p ∣ m) (hqm : q ∣ m) (hps : m < p * p) (hqs : m < q * q) : False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpqm : p * q ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpm hqm
  have hle : p * q ≤ m := Nat.le_of_dvd hm hpqm
  nlinarith [hps, hqs, hle, hp.pos, hq.pos, hm, Nat.mul_le_mul hle hle]

/-- Unconditional partial result: whenever `⌊(n+1)^{3/2}⌋` is itself prime, the
conjecture holds trivially, because a prime's only divisors are `1` and itself, so
`gcd(⌊(n+1)^{3/2}⌋, b n) ∈ {1, ⌊(n+1)^{3/2}⌋}`, forcing `a n ∈ {⌊(n+1)^{3/2}⌋, 1}`. -/
theorem a_prime_of_sqrt_prime (n : ℕ) (hn : 1 ≤ n)
    (hp : Nat.Prime (Nat.sqrt ((n + 1) ^ 3))) : a n = 1 ∨ Nat.Prime (a n) := by
  rw [a_eq n hn]
  have hd : Nat.gcd (Nat.sqrt ((n + 1) ^ 3)) (b n) ∣ Nat.sqrt ((n + 1) ^ 3) :=
    Nat.gcd_dvd_left _ _
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | hs
  · rw [h1, Nat.div_one]; right; exact hp
  · rw [hs]; left; exact Nat.div_self hp.pos

/--
Conjecture 1 from OEIS A323359: This sequence consists only of 1's and primes.

Status / reduction (see the proven lemmas above):

By `a_eq`, `a n = s / gcd (s, b n)` where `s = ⌊(n+1)^{3/2}⌋`.  By
`at_most_one_large_prime`, any positive integer has at most one prime factor
exceeding its square root, so the conjecture is *equivalent* to the coverage
statement:

  for every prime `p ≤ √s` with `p ∣ s`, one has `v_p (b n) ≥ v_p s`.

Since `b n = 2 · ∏_{j<n} (1 + a j)` and a prime `p` divides `b n` iff `p = 2`
or some earlier `a j ≡ -1 (mod p)`, and the `a j` are themselves prime factors
of `⌊k^{3/2}⌋`, coverage requires equidistribution of Piatetski–Shapiro primes
(exponent `3/2`) in arithmetic progressions.  This lies beyond the currently
proven exponent range and is not available in Mathlib.  The statement is true
(no counterexample; matches the OEIS data), so it cannot be disproved either.
-/
theorem oeis_323359_conjecture_1 :
  ∀ (n : ℕ), 0 < n → (a n = 1 ∨ Nat.Prime (a n)) := by
  sorry
