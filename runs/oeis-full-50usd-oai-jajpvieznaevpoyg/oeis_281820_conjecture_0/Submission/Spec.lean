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

/--
A281820 Conjecture: Sum_{n >= k+1} 1/(n^3*(n^2 - 1)^2*(n^2 - 4)^2*...*(n^2 - k^2)^2) = Sum_{n >= k+1} 1/(n*binomial(n,k)^2*binomial(n+k,k)^2*(n-k)^2) = zeta(3) - A281820(k)/A281821(k). - _Peter Bala_, Jan 17 2022
-/
private lemma conj_term_2_two_eq (n : ℕ) : conj_term_2 2 n = 16 * conj_term_1 2 n := by
  by_cases hn : n ≤ 2
  · simp [conj_term_1, conj_term_2, hn]
  · have h3 : 3 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h3
    simp [conj_term_1, conj_term_2, Finset.prod_Icc_succ_top, Nat.cast_choose_two]
    field_simp
    ring_nf

private lemma conj_term_1_two_nonneg (n : ℕ) : 0 ≤ conj_term_1 2 n := by
  by_cases hn : n ≤ 2
  · simp [conj_term_1, hn]
  · have h3 : 3 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h3
    simp [conj_term_1, Finset.prod_Icc_succ_top]
    positivity

private lemma conj_term_1_two_le (n : ℕ) : conj_term_1 2 n ≤ 1 / (n : ℝ) ^ 3 := by
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num [conj_term_1]
  · have h3 : 3 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h3
    have hmnot : ¬ 3 + m ≤ 2 := by omega
    simp [conj_term_1, Finset.prod_Icc_succ_top, hmnot]
    field_simp
    ring_nf
    apply inv_le_one_of_one_le₀
    have htail : 0 ≤ (↑m * 6240 + ↑m ^ 2 * 10004 + ↑m ^ 3 * 8604 + ↑m ^ 4 * 4353 + ↑m ^ 5 * 1332 + ↑m ^ 6 * 242 + ↑m ^ 7 * 24 + (↑m : ℝ) ^ 8) := by
      positivity
    linarith

private lemma conj_term_1_two_summable : Summable (fun n : ℕ => conj_term_1 2 n) := by
  exact Summable.of_nonneg_of_le
    (g := fun n : ℕ => conj_term_1 2 n)
    (f := fun n : ℕ => 1 / (n : ℝ) ^ 3)
    conj_term_1_two_nonneg conj_term_1_two_le
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))

private lemma conj_term_1_two_tsum_pos : 0 < (∑' n : ℕ, conj_term_1 2 n) := by
  exact conj_term_1_two_summable.tsum_pos conj_term_1_two_nonneg 3
    (by norm_num [conj_term_1, Finset.prod_Icc_succ_top])

theorem oeis_281820_conjecture_0.disproof :
    ¬ ∀ (k : ℕ), 1 ≤ k →
      (∑' n : ℕ, conj_term_1 k n) = (∑' n : ℕ, conj_term_2 k n) ∧
      (∑' n : ℕ, conj_term_1 k n) = zeta_three - (a k : ℝ) / (A281821 k : ℝ) := by
  intro h
  have heq : (∑' n : ℕ, conj_term_1 2 n) = (∑' n : ℕ, conj_term_2 2 n) := (h 2 (by norm_num)).1
  have hrel : (∑' n : ℕ, conj_term_2 2 n) = 16 * (∑' n : ℕ, conj_term_1 2 n) := by
    calc
      (∑' n : ℕ, conj_term_2 2 n) = (∑' n : ℕ, 16 * conj_term_1 2 n) := by
        exact tsum_congr (fun n => conj_term_2_two_eq n)
      _ = 16 * (∑' n : ℕ, conj_term_1 2 n) := by
        exact tsum_mul_left
  have hzero : (∑' n : ℕ, conj_term_1 2 n) = 0 := by
    rw [hrel] at heq
    nlinarith
  nlinarith [conj_term_1_two_tsum_pos]
