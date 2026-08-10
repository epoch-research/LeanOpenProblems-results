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

lemma choose_zero (n : ℕ) : Nat.choose n 0 = 1 := by
  cases n <;> rfl

lemma choose_one (n : ℕ) : Nat.choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, ih, choose_zero]
    omega

lemma choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [Nat.choose_succ_succ, Nat.mul_add, ih, choose_one]
      have h1 : n + 1 - 1 = n := by omega
      have h2 : n + 2 - 1 = n + 1 := by omega
      rw [h1, h2]
      ring

lemma choose_two_real (n : ℕ) (hn : 2 ≤ n) : (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have h := congr_arg (fun x : ℕ => (x : ℝ)) (choose_two n)
  push_cast at h
  have h3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [h3] at h
  linarith



lemma conj_term_2_two (n : ℕ) :
    conj_term_2 2 n = if n ≤ 2 then 0 else 16 / ((n : ℝ) ^ 3 * (((n : ℝ)^2 - 1)^2 * ((n : ℝ)^2 - 4)^2)) := by
  unfold conj_term_2
  split_ifs with h
  · rfl
  · simp only
    have hn : 2 ≤ n := by omega
    have hn2 : 2 ≤ n + 2 := by omega
    rw [choose_two_real n hn, choose_two_real (n + 2) hn2]
    push_cast
    have h_sub : (n : ℝ) + 2 - 1 = (n : ℝ) + 1 := by ring
    rw [h_sub]
    have hn3_nat : n ≥ 3 := by omega
    have hn3 : (n : ℝ) ≥ 3 := Nat.cast_le.mpr hn3_nat
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn2_ne : (n : ℝ) - 2 ≠ 0 := by linarith
    have hnp1 : (n : ℝ) + 1 ≠ 0 := by linarith
    have hnp2 : (n : ℝ) + 2 ≠ 0 := by linarith
    have hn_1 : (n : ℝ)^2 - 1 ≠ 0 := by nlinarith
    have hn_4 : (n : ℝ)^2 - 4 ≠ 0 := by nlinarith
    field_simp [hn0, hn1, hn2_ne, hnp1, hnp2, hn_1, hn_4]
    ring





lemma conj_term_1_nonneg (k : ℕ) (n : ℕ) : 0 ≤ conj_term_1 k n := by
  unfold conj_term_1
  split_ifs with h
  · linarith
  · positivity


lemma prod_icc_one_two (f : ℕ → ℝ) :
    ∏ j ∈ Finset.Icc 1 2, f j = f 1 * f 2 := by
  have h : Finset.Icc 1 2 = {1, 2} := rfl
  rw [h]
  simp

lemma conj_term_1_two (n : ℕ) :
    conj_term_1 2 n = if n ≤ 2 then 0 else 1 / ((n : ℝ) ^ 3 * (((n : ℝ)^2 - 1)^2 * ((n : ℝ)^2 - 4)^2)) := by
  unfold conj_term_1
  split_ifs with h
  · rfl
  · simp only
    rw [prod_icc_one_two]
    ring_nf

lemma conj_term_1_le_inv_cubed (n : ℕ) : conj_term_1 2 n ≤ 1 / (n : ℝ)^3 := by
  rw [conj_term_1_two]
  split_ifs with h
  · positivity
  · have hn3_nat : n ≥ 3 := by omega
    have hn : (n : ℝ) ≥ 3 := Nat.cast_le.mpr hn3_nat
    have h_den : (n : ℝ)^3 * (((n : ℝ)^2 - 1)^2 * ((n : ℝ)^2 - 4)^2) ≥ (n : ℝ)^3 := by
      have h1 : (n : ℝ)^2 - 1 ≥ 8 := by nlinarith
      have h2 : (n : ℝ)^2 - 4 ≥ 5 := by nlinarith
      have h1_sq : ((n : ℝ)^2 - 1)^2 ≥ 64 := by nlinarith
      have h2_sq : ((n : ℝ)^2 - 4)^2 ≥ 25 := by nlinarith
      have h_prod : ((n : ℝ)^2 - 1)^2 * ((n : ℝ)^2 - 4)^2 ≥ 1 := by nlinarith
      have : (n : ℝ)^3 > 0 := by nlinarith
      nlinarith
    have hn3_pos : (n : ℝ)^3 > 0 := by nlinarith
    have h_den_pos : (n : ℝ)^3 * (((n : ℝ)^2 - 1)^2 * ((n : ℝ)^2 - 4)^2) > 0 := by
      have h1 : (n : ℝ)^2 - 1 ≥ 8 := by nlinarith
      have h2 : (n : ℝ)^2 - 4 ≥ 5 := by nlinarith
      have : (n : ℝ)^3 ≥ 27 := by nlinarith
      nlinarith
    exact (one_div_le_one_div h_den_pos hn3_pos).mpr h_den

lemma conj_term_1_summable : Summable (conj_term_1 2) := by
  have h_inv : Summable (fun n : ℕ => 1 / (n : ℝ)^3) := summable_one_div_nat_pow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le (conj_term_1_nonneg 2) conj_term_1_le_inv_cubed h_inv

lemma conj_term_1_sum_pos : (∑' n, conj_term_1 2 n) > 0 := by
  have h_le := Summable.le_tsum conj_term_1_summable 3 (fun j _ => conj_term_1_nonneg 2 j)
  have h3 : conj_term_1 2 3 > 0 := by
    rw [conj_term_1_two]
    norm_num
  linarith




lemma conj_term_2_eq_16_mul (n : ℕ) : conj_term_2 2 n = 16 * conj_term_1 2 n := by
  rw [conj_term_1_two, conj_term_2_two]
  split_ifs with h
  · ring
  · ring


set_option linter.unusedVariables false

/--
A281820 Conjecture: Sum_{n >= k+1} 1/(n^3*(n^2 - 1)^2*(n^2 - 4)^2*...*(n^2 - k^2)^2) = Sum_{n >= k+1} 1/(n*binomial(n,k)^2*binomial(n+k,k)^2*(n-k)^2) = zeta(3) - A281820(k)/A281821(k). - _Peter Bala_, Jan 17 2022
-/
theorem oeis_281820_conjecture_0.disproof :
    ¬ ∀ (k : ℕ) (hk : 1 ≤ k),
      (∑' n : ℕ, conj_term_1 k n) = (∑' n : ℕ, conj_term_2 k n) ∧
      (∑' n : ℕ, conj_term_1 k n) = zeta_three - (a k : ℝ) / (A281821 k : ℝ) := by
  intro h
  have h_spec := h 2 (by norm_num)
  have h_eq : (∑' n : ℕ, conj_term_1 2 n) = (∑' n : ℕ, conj_term_2 2 n) := h_spec.1
  have h_16 : (∑' n : ℕ, conj_term_2 2 n) = (∑' n : ℕ, 16 * conj_term_1 2 n) := congr_arg tsum (funext conj_term_2_eq_16_mul)
  rw [tsum_mul_left] at h_16
  have h_contr : (∑' n : ℕ, conj_term_1 2 n) = 16 * (∑' n : ℕ, conj_term_1 2 n) := h_eq.trans h_16
  have h_sum_pos := conj_term_1_sum_pos
  linarith
