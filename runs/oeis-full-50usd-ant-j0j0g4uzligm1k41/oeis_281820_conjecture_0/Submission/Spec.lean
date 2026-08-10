import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Rat

/--
The $k$-th term of the sum in A281820, defined to be 0 when $k=0$.
$$ T_k = \frac{30k-11}{4(2k-1)k^3 \binom{2k}{k}^2} $$
-/
def A281820_term (k : ℕ) : ℚ :=
  if k = 0 then 0
  else
    let k_q : ℚ := k

    -- Numerator: 30k - 11
    let numerator : ℚ := (30 : ℚ) * k_q - 11

    -- Denominator: 4 * (2k-1) * k^3 * binomial(2k,k)^2
    let denominator : ℚ :=
      (4 : ℚ) * ((2 : ℚ) * k_q - 1) * (k_q ^ 3) * ((Nat.choose (2 * k) k) : ℚ) ^ 2

    numerator / denominator

/--
A281820: Numerator of $\sum_{k=1}^n \frac{30k-11}{4(2k-1)k^3 \binom{2k}{k}^2}$.
The sum over $k=1$ to $n$ is computed using $\sum_{k=0}^n$ since $\text{A281820\_term}(0) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let sum_q : ℚ := Finset.sum (Finset.range (n + 1)) A281820_term
  sum_q.num.natAbs

/--
A281821: Denominator of $\sum_{k=1}^n \frac{30k-11}{4(2k-1)k^3 \binom{2k}{k}^2}$.
-/
noncomputable def A281821 (n : ℕ) : ℕ :=
  let sum_q : ℚ := Finset.sum (Finset.range (n + 1)) A281820_term
  sum_q.den

open Real BigOperators

/-- Apery's constant $\zeta(3) = \sum_{n=1}^\infty 1/n^3$. -/
noncomputable def zeta_three : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (n : ℝ) ^ 3

/--
The term for the first sum in the conjecture:
$$ \frac{1}{n^3 \prod_{j=1}^k (n^2 - j^2)^2} $$
Note: This term is only defined for $n > k$.
-/
noncomputable def conj_term_1 (k n : ℕ) : ℝ :=
  if n ≤ k then 0
  else
    let n_r : ℝ := n
    -- The product $\prod_{j=1}^k$
    let product_sq_terms : ℝ := Finset.prod (Finset.Icc 1 k) (fun j : ℕ => (n_r^2 - ((j : ℝ) ^ 2)) ^ 2)
    1 / (n_r ^ 3 * product_sq_terms)

/--
The term for the second sum in the conjecture:
$$ \frac{1}{n \binom{n}{k}^2 \binom{n+k}{k}^2 (n-k)^2} $$
Note: This term is only defined for $n > k$.
-/
noncomputable def conj_term_2 (k n : ℕ) : ℝ :=
  if n ≤ k then 0
  else
    let n_r : ℝ := n
    let k_r : ℝ := k

    -- $\binom{n}{k}^2$
    let binom_nk_sq : ℝ := ((Nat.choose n k) : ℝ) ^ 2

    -- $\binom{n+k}{k}^2$
    let binom_npk_sq : ℝ := ((Nat.choose (n + k) k) : ℝ) ^ 2

    -- $(n-k)^2$
    let diff_sq : ℝ := (n_r - k_r) ^ 2

    1 / (n_r * binom_nk_sq * binom_npk_sq * diff_sq)

/-
A281820 Conjecture: Sum_{n >= k+1} 1/(n^3*(n^2 - 1)^2*(n^2 - 4)^2*...*(n^2 - k^2)^2) = Sum_{n >= k+1} 1/(n*binomial(n,k)^2*binomial(n+k,k)^2*(n-k)^2) = zeta(3) - A281820(k)/A281821(k). - _Peter Bala_, Jan 17 2022

The conjecture as formalised is FALSE: see `oeis_281820_conjecture_0.disproof` below.
-/
/-- Explicit closed form of `conj_term_1 2 n` for `n ≥ 3`. -/
theorem conj_term_1_two_val (n : ℕ) (hn : 3 ≤ n) :
    conj_term_1 2 n = 1 / ((n:ℝ)^3 * (((n:ℝ)^2 - 1)^2 * ((n:ℝ)^2 - 4)^2)) := by
  have hle : ¬ n ≤ 2 := by omega
  simp only [conj_term_1, hle, if_false]
  have hprod : Finset.prod (Finset.Icc 1 2) (fun j : ℕ => ((n:ℝ)^2 - ((j : ℝ) ^ 2)) ^ 2)
      = ((n:ℝ)^2 - 1)^2 * ((n:ℝ)^2 - 4)^2 := by
    have : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
    norm_num
  rw [hprod]

/-- For `k = 2` the second summand is `16 = (2!)^4` times the first summand,
    pointwise, so the two series in the conjecture cannot be equal. -/
theorem conj_term_two_eq (n : ℕ) : conj_term_2 2 n = 16 * conj_term_1 2 n := by
  by_cases h1 : n ≤ 2
  · simp only [conj_term_1, conj_term_2, h1, if_true]
    ring
  · have hle : ¬ n ≤ 2 := h1
    have h : 3 ≤ n := by omega
    have hr : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    simp only [conj_term_1, conj_term_2, hle, if_false]
    have hprod : Finset.prod (Finset.Icc 1 2) (fun j : ℕ => ((n:ℝ)^2 - ((j : ℝ) ^ 2)) ^ 2)
        = ((n:ℝ)^2 - 1)^2 * ((n:ℝ)^2 - 4)^2 := by
      have : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
      rw [this, Finset.prod_pair (by norm_num)]
      norm_num
    rw [hprod]
    have hc1 : ((Nat.choose n 2 : ℝ)) = (n:ℝ) * ((n:ℝ) - 1) / 2 := Nat.cast_choose_two (K := ℝ) n
    have hc2 : ((Nat.choose (n+2) 2 : ℝ)) = ((n:ℝ)+2) * ((n:ℝ)+1) / 2 := by
      have := Nat.cast_choose_two (K := ℝ) (n+2)
      push_cast at this ⊢
      linarith [this]
    rw [hc1, hc2]
    have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (by linarith)
    have h1' : (n:ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    have h2 : (n:ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
    have h3 : (n:ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
    have h4 : (n:ℝ) + 2 ≠ 0 := ne_of_gt (by linarith)
    have h5 : (n:ℝ)^2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
    have h6 : (n:ℝ)^2 - 4 ≠ 0 := ne_of_gt (by nlinarith)
    push_cast
    rw [mul_one_div]
    rw [div_eq_div_iff]
    · ring
    · have hA : (n:ℝ) * ((n:ℝ) - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero hn0 h1') two_ne_zero
      have hB : ((n:ℝ) + 2) * ((n:ℝ) + 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero h4 h3) two_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn0 (pow_ne_zero 2 hA)) (pow_ne_zero 2 hB)) (pow_ne_zero 2 h2)
    · exact mul_ne_zero (pow_ne_zero 3 hn0) (mul_ne_zero (pow_ne_zero 2 h5) (pow_ne_zero 2 h6))

theorem conj_term_1_two_nonneg (n : ℕ) : 0 ≤ conj_term_1 2 n := by
  unfold conj_term_1
  split
  · exact le_refl 0
  · positivity

theorem conj_term_1_two_bound (n : ℕ) : conj_term_1 2 n ≤ 1 / (n:ℝ)^3 := by
  by_cases h1 : n ≤ 2
  · rw [conj_term_1]
    simp only [h1, if_true]
    positivity
  · have hn : 3 ≤ n := by omega
    have hr : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    rw [conj_term_1_two_val n hn]
    have hn3 : (0:ℝ) < (n:ℝ)^3 := by positivity
    have hn2 : (9:ℝ) ≤ (n:ℝ)^2 := by nlinarith
    have ha2 : (64:ℝ) ≤ ((n:ℝ)^2 - 1)^2 := by nlinarith [hn2]
    have hb2 : (25:ℝ) ≤ ((n:ℝ)^2 - 4)^2 := by nlinarith [hn2]
    have hP : (1:ℝ) ≤ ((n:ℝ)^2 - 1)^2 * ((n:ℝ)^2 - 4)^2 := by nlinarith [ha2, hb2]
    have hle : (n:ℝ)^3 ≤ (n:ℝ)^3 * (((n:ℝ)^2 - 1)^2 * ((n:ℝ)^2 - 4)^2) :=
      le_mul_of_one_le_right (le_of_lt hn3) hP
    exact one_div_le_one_div_of_le hn3 hle

theorem conj_term_1_two_summable : Summable (fun n => conj_term_1 2 n) := by
  apply Summable.of_nonneg_of_le conj_term_1_two_nonneg conj_term_1_two_bound
  exact (summable_one_div_nat_pow).mpr (by norm_num)

theorem conj_term_1_two_pos_three : 0 < conj_term_1 2 3 := by
  rw [conj_term_1_two_val 3 (le_refl 3)]
  norm_num

/--
The conjecture is **false**.  For every `k ≥ 2` the general term of the second
series equals `(k!)^4` times the general term of the first series, so the two
series in the first claimed equality differ by a nonzero factor `(k!)^4 ≠ 1`.
We disprove it explicitly at `k = 2`, where the factor is `2!^4 = 16`.
-/
theorem oeis_281820_conjecture_0.disproof :
    ¬ ∀ (k : ℕ), 1 ≤ k →
      (∑' n : ℕ, conj_term_1 k n) = (∑' n : ℕ, conj_term_2 k n) ∧
      (∑' n : ℕ, conj_term_1 k n) = zeta_three - (a k : ℝ) / (A281821 k : ℝ) := by
  intro h
  obtain ⟨heq, _⟩ := h 2 (by norm_num)
  have hStot : 0 < ∑' n, conj_term_1 2 n :=
    conj_term_1_two_summable.tsum_pos conj_term_1_two_nonneg 3 conj_term_1_two_pos_three
  have hsum2 : (∑' n, conj_term_2 2 n) = 16 * ∑' n, conj_term_1 2 n := by
    rw [← tsum_mul_left]
    exact tsum_congr conj_term_two_eq
  rw [hsum2] at heq
  linarith
