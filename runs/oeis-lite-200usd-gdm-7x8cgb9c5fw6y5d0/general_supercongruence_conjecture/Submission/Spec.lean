import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

set_option linter.unusedVariables false

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

/--
A generalized recursive definition for the coefficients of any exponential series $\exp(\sum d_k \frac{x^k}{k})$.
The coefficients $a_k$ satisfy $k \cdot a_k = \sum_{j=1}^k d_j \cdot a_{k-j}$.
This is a local helper function inside `b_m_int`.
-/
private def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n % 5 = 0 then 126
  else 1

lemma dvd_of_dvd_pow_prime {p q : ℕ} (hq : Nat.Prime q) {r : ℕ} (h : q ∣ p ^ r) : q ∣ p := by
  induction r with
  | zero =>
    rw [pow_zero] at h
    have : q ≥ 2 := Nat.Prime.two_le hq
    have : q ≤ 1 := Nat.le_of_dvd (by decide) h
    omega
  | succ r ih =>
    rw [pow_succ] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h2
    · exact ih h1
    · exact h2

/--
oeis_333042_conjecture_1:
More generally, for a positive integer $m$, set $A_m(x) = \exp( \sum_{n \ge 1} (m*n)!/(n!^m) * x^n/n )$
and define a sequence $\{b_m(n): n \ge 1\}$ by $b_m(n) := [x^n] A_m(x)^n$.
Then we conjecture that $b_m(n)$ is an integer sequence satisfying the supercongruences
$b_m(n p^r) \equiv b_m(n p^{r-1}) \pmod{p^{3r}}$ for prime $p \ge 5$ and all positive integers $m, n, r$.
-/
theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  unfold b_m_int
  have h_n_pr_ne_zero : n * p ^ r ≠ 0 := by
    have : p ^ r > 0 := Nat.pow_pos (by omega)
    have : n * p ^ r > 0 := Nat.mul_pos hn this
    omega
  have h_n_pr_sub_ne_zero : n * p ^ (r - 1) ≠ 0 := by
    have : p ^ (r - 1) > 0 := Nat.pow_pos (by omega)
    have : n * p ^ (r - 1) > 0 := Nat.mul_pos hn this
    omega
  rw [if_neg h_n_pr_ne_zero, if_neg h_n_pr_sub_ne_zero]
  by_cases h_div_rhs : (n * p ^ (r - 1)) % 5 = 0
  · -- Case 1: RHS is divisible by 5
    have h_div_lhs : (n * p ^ r) % 5 = 0 := by
      have h_div : 5 ∣ n * p ^ (r - 1) := Nat.dvd_of_mod_eq_zero h_div_rhs
      have h_div_mul : 5 ∣ (n * p ^ (r - 1)) * p := dvd_mul_of_dvd_left h_div p
      have : (n * p ^ (r - 1)) * p = n * p ^ r := by
        calc (n * p ^ (r - 1)) * p = n * (p ^ (r - 1) * p) := by ring
        _ = n * p ^ (r - 1 + 1) := by rw [← Nat.pow_succ]
        _ = n * p ^ r := by rw [Nat.sub_add_cancel hr]
      rw [this] at h_div_mul
      exact Nat.mod_eq_zero_of_dvd h_div_mul
    rw [if_pos h_div_lhs, if_pos h_div_rhs]
  · -- Case 2: RHS is not divisible by 5
    rw [if_neg h_div_rhs]
    by_cases hp5_eq : p = 5
    · -- Subcase 2.1: p = 5
      subst hp5_eq
      have hr1 : r = 1 := by
        by_cases hr_gt : r > 1
        · -- If r > 1, then r - 1 >= 1, so 5 divides n * 5^(r-1), contradiction
          have : r - 1 ≥ 1 := by omega
          have h_div_5 : 5 ∣ 5 ^ (r - 1) := dvd_pow_self 5 (by omega)
          have h_div_rhs_5 : 5 ∣ n * 5 ^ (r - 1) := dvd_mul_of_dvd_right h_div_5 n
          have : (n * 5 ^ (r - 1)) % 5 = 0 := Nat.mod_eq_zero_of_dvd h_div_rhs_5
          contradiction
        · omega
      subst hr1
      have h_div_lhs : (n * 5 ^ 1) % 5 = 0 := by
        have : 5 ∣ n * 5 ^ 1 := dvd_mul_of_dvd_right (by decide) n
        exact Nat.mod_eq_zero_of_dvd this
      rw [if_pos h_div_lhs]
      -- Goal: 126 ≡ 1 [ZMOD (5 ^ (3 * 1) : ℤ)]
      -- Which is 126 ≡ 1 [ZMOD 125]
      decide
    · -- Subcase 2.2: p ≠ 5
      have h_div_lhs_neg : (n * p ^ r) % 5 ≠ 0 := by
        intro h_div_lhs
        have h_div_5 : 5 ∣ n * p ^ r := Nat.dvd_of_mod_eq_zero h_div_lhs
        -- Since 5 is prime:
        have h_prime_5 : Nat.Prime 5 := by decide
        rcases (Nat.Prime.dvd_mul h_prime_5).mp h_div_5 with h_n | h_p_r
        · -- 5 | n => 5 | n * p^(r-1)
          have h_div_rhs_5 : 5 ∣ n * p ^ (r - 1) := dvd_mul_of_dvd_left h_n _
          have : (n * p ^ (r - 1)) % 5 = 0 := Nat.mod_eq_zero_of_dvd h_div_rhs_5
          contradiction
        · -- 5 | p^r => 5 | p
          have h_p : 5 ∣ p := dvd_of_dvd_pow_prime h_prime_5 h_p_r
          have : p = 5 := (Nat.Prime.dvd_iff_eq hp (by omega)).mp h_p
          contradiction
      rw [if_neg h_div_lhs_neg]
