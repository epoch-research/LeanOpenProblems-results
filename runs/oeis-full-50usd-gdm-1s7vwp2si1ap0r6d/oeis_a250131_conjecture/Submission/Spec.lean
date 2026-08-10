import FormalConjectures.Util.ProblemImports

open Nat

/--
A250131: $a(n)$ is the odd part of the digital sum of $3^n$ divided by the maximal possible power of $3$.
The sequence is defined by the formula derived from the PARI code:
$$a(n) = \frac{S(3^n)}{3^{\nu_3(S(3^n))} \cdot 2^{\nu_2(S(3^n))}}$$
where $S(m)$ is the sum of base 10 digits of $m$, and $\nu_p(m)$ is the $\mathrm{p}$-adic valuation of $m$.
-/
def a (n : ℕ) : ℕ :=
  let d := List.sum (Nat.digits 10 (3 ^ n))
  let v3 := padicValNat 3 d
  let v2 := padicValNat 2 d
  d / (3 ^ v3 * 2 ^ v2)

/-- Sequence b(n) related to A250131: b(1)=2, b(2)=3, and for n>=3, b(n)=a(n-2). -/
def b (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | n' + 3 => a (n' + 1)

/-- The set of indices $n \ge 1$ such that $b(n) \ne 1$ and $b(n)$ is not a multiple of any $b(k)$ for $1 \le k < n$ where $b(k) \ne 1$.
This formalizes the "Eratosthenes-like sieve" on the sequence b(n) after removing 1's, by insisting that a term must not be divisible by any preceding non-one term. -/
def sieved_indices : Set ℕ :=
  { n | 1 ≤ n ∧ b n ≠ 1 ∧ ∀ k, (1 ≤ k ∧ k < n ∧ b k ≠ 1) → ¬ (b k ∣ b n) }

/--
Conjecture A250131: Consider the sequence {b(n)}, such that b(1)=2, b(2)=3, and for n>=3, b(n)=a(n-2).
We conjecture that, if we apply the Eratosthenes-like sieve to b(n) and remove 1's, then we obtain a sequence of primes.
-/
theorem oeis_a250131_conjecture :
    ∀ n : ℕ, n ∈ sieved_indices → Nat.Prime (b n) := by
  intro n hn
  have hn_ge : 1 ≤ n := hn.1
  have h_ne_one : b n ≠ 1 := hn.2.1
  have h_dvd : ∀ k, (1 ≤ k ∧ k < n ∧ b k ≠ 1) → ¬ (b k ∣ b n) := hn.2.2
  have h_pos : b n ≠ 0 := by
    intro hb0
    by_cases hn1 : n = 1
    · subst hn1
      -- b 1 = 2, so b 1 ≠ 0
      contradiction
    · -- n ≥ 2, so 1 < n
      have hk1 : 1 ≤ 1 := by omega
      have hk2 : 1 < n := by omega
      have hk_ne_one : b 1 ≠ 1 := by decide
      have h_div_contr := h_dvd 1 ⟨hk1, hk2, hk_ne_one⟩
      apply h_div_contr
      rw [hb0]
      exact dvd_zero (b 1)
  have h_two_le : 2 ≤ b n := by omega
  rw [Nat.prime_def_lt']
  refine ⟨h_two_le, ?_⟩
  intro m hm_ge hm_lt h_m_dvd
  have h_m_ne_one : m ≠ 1 := by omega
  have ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h_m_ne_one
  have hp_dvd_bn : p ∣ b n := Nat.dvd_trans hp_dvd h_m_dvd
  have hp_pos : 0 < b n := Nat.pos_of_ne_zero h_pos
  have hm_pos : 0 < m := by omega
  have hp_le_m : p ≤ m := Nat.le_of_dvd hm_pos hp_dvd
  have hp_lt : p < b n := by omega
  have ⟨k, hk1, hk2, hk3⟩ : ∃ k, 1 ≤ k ∧ k < n ∧ b k = p := sorry
  have hk_ne_one : b k ≠ 1 := by
    rw [hk3]
    exact Nat.Prime.ne_one hp_prime
  have h_div_contr : ¬ (b k ∣ b n) := h_dvd k ⟨hk1, hk2, hk_ne_one⟩
  apply h_div_contr
  rw [hk3]
  exact hp_dvd_bn








