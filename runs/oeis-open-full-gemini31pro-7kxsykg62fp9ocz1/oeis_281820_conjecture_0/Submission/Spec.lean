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
theorem oeis_281820_conjecture_0 (k : ℕ) (hk : 1 ≤ k) :
    (∑' n : ℕ, conj_term_1 k n) = (∑' n : ℕ, conj_term_2 k n) ∧
    (∑' n : ℕ, conj_term_1 k n) = zeta_three - (a k : ℝ) / (A281821 k : ℝ) :=
  by sorry


lemma choose_two_mul_two (n : ℕ) : (n.choose 2 : ℝ) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
  induction' n with n ih
  · simp
  · have h1 : ((n + 1).choose 2 : ℝ) = (n.choose 2 : ℝ) + (n.choose 1 : ℝ) := by
      have : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      have this2 : (n + 1).choose 2 = n.choose 2 + n.choose 1 := by rw [this, add_comm]
      exact_mod_cast this2
    rw [h1, add_mul, ih]
    have h2 : (n.choose 1 : ℝ) = n := by
      have : n.choose 1 = n := Nat.choose_one_right n
      exact_mod_cast this
    rw [h2]
    push_cast
    ring

lemma choose_two_real (n : ℕ) : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  calc
    (n.choose 2 : ℝ) = (n.choose 2 : ℝ) * 2 / 2 := by ring
    _ = (n : ℝ) * ((n : ℝ) - 1) / 2 := by rw [choose_two_mul_two n]

lemma conj_term_1_eq (n : ℕ) (hn : 2 < n) :
  conj_term_1 2 n = 1 / ((n : ℝ) ^ 3 * (((n : ℝ)^2 - 1^2)^2 * ((n : ℝ)^2 - 2^2)^2)) := by
  dsimp [conj_term_1]
  rw [if_neg (by omega)]
  have h1 : (Finset.Icc 1 2) = {1, 2} := rfl
  rw [h1]
  simp

lemma conj_term_2_eq (n : ℕ) (hn : 2 < n) :
  conj_term_2 2 n = 1 / ((n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2)^2 * (((n : ℝ) + 2) * (((n : ℝ) + 2) - 1) / 2)^2 * ((n : ℝ) - 2)^2) := by
  dsimp [conj_term_2]
  rw [if_neg (by omega)]
  have h1 : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := choose_two_real n
  have h2 : ((n + 2).choose 2 : ℝ) = ((n + 2 : ℝ)) * (((n + 2 : ℝ)) - 1) / 2 := by
    have := choose_two_real (n + 2)
    push_cast at this
    exact this
  rw [h1, h2]

lemma div_16 (X : ℝ) : 1 / (X / 16) = 16 * (1 / X) := by
  calc
    1 / (X / 16) = 16 / X := by ring
    _ = 16 * (1 / X) := by ring

lemma conj_term_2_eq_16_mul_1_real (n : ℝ) :
  1 / (n * (n * (n - 1) / 2)^2 * ((n + 2) * ((n + 2) - 1) / 2)^2 * (n - 2)^2) =
  16 * (1 / (n ^ 3 * ((n^2 - 1^2)^2 * (n^2 - 2^2)^2))) := by
  have h_den : n * (n * (n - 1) / 2)^2 * ((n + 2) * ((n + 2) - 1) / 2)^2 * (n - 2)^2 =
               (n ^ 3 * ((n^2 - 1^2)^2 * (n^2 - 2^2)^2)) / 16 := by
    ring
  rw [h_den, div_16]

lemma conj_term_2_eq_16_mul_1 (n : ℕ) : conj_term_2 2 n = 16 * conj_term_1 2 n := by
  by_cases hn : n ≤ 2
  · have h1 : conj_term_1 2 n = 0 := by dsimp [conj_term_1]; rw [if_pos hn]
    have h2 : conj_term_2 2 n = 0 := by dsimp [conj_term_2]; rw [if_pos hn]
    rw [h1, h2, mul_zero]
  · push_neg at hn
    rw [conj_term_1_eq n hn, conj_term_2_eq n hn]
    exact conj_term_2_eq_16_mul_1_real n

lemma tsum_conj_term_2 : (∑' n : ℕ, conj_term_2 2 n) = 16 * (∑' n : ℕ, conj_term_1 2 n) := by
  have : (fun n : ℕ => conj_term_2 2 n) = fun n : ℕ => 16 * conj_term_1 2 n := by
    funext n
    exact conj_term_2_eq_16_mul_1 n
  rw [this, tsum_mul_left]

lemma conj_term_1_le (n : ℕ) : conj_term_1 2 n ≤ ((n : ℝ) ^ 3)⁻¹ := by
  by_cases hn : n ≤ 2
  · have h1 : conj_term_1 2 n = 0 := by dsimp [conj_term_1]; rw [if_pos hn]
    rw [h1]
    positivity
  · push_neg at hn
    rw [conj_term_1_eq n hn]
    have hn_pos : 0 < (n : ℝ) := by exact Nat.cast_pos.mpr (by omega)
    have h1 : 1 ≤ ((n : ℝ)^2 - 1^2)^2 * ((n : ℝ)^2 - 2^2)^2 := by
      have hn3 : 3 ≤ (n : ℝ) := by exact_mod_cast hn
      have hn2_1 : 8 ≤ (n : ℝ)^2 - 1^2 := by nlinarith
      have hn2_2 : 5 ≤ (n : ℝ)^2 - 2^2 := by nlinarith
      nlinarith
    have h2 : (n : ℝ) ^ 3 * 1 ≤ (n : ℝ) ^ 3 * (((n : ℝ)^2 - 1^2)^2 * ((n : ℝ)^2 - 2^2)^2) := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [mul_one] at h2
    have h3 : 1 / ((n : ℝ) ^ 3 * (((n : ℝ)^2 - 1^2)^2 * ((n : ℝ)^2 - 2^2)^2)) ≤ 1 / ((n : ℝ) ^ 3) := by
      apply one_div_le_one_div_of_le (by positivity) h2
    calc
      1 / ((n : ℝ) ^ 3 * (((n : ℝ)^2 - 1^2)^2 * ((n : ℝ)^2 - 2^2)^2)) ≤ 1 / ((n : ℝ) ^ 3) := h3
      _ = ((n : ℝ) ^ 3)⁻¹ := by rw [one_div]

lemma conj_term_1_nonneg (n : ℕ) : 0 ≤ conj_term_1 2 n := by
  by_cases hn : n ≤ 2
  · have h1 : conj_term_1 2 n = 0 := by dsimp [conj_term_1]; rw [if_pos hn]
    rw [h1]
  · push_neg at hn
    rw [conj_term_1_eq n hn]
    positivity

lemma conj_term_1_summable : Summable (conj_term_1 2) := by
  have h_sum : Summable (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) := by
    have h : (Summable fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) ↔ 1 < 3 := @Real.summable_nat_pow_inv 3
    rw [h]
    norm_num
  exact Summable.of_nonneg_of_le conj_term_1_nonneg conj_term_1_le h_sum

lemma sum_pos : 0 < (∑' n : ℕ, conj_term_1 2 n) := by
  have h_le : ∑ n ∈ {3}, conj_term_1 2 n ≤ ∑' n : ℕ, conj_term_1 2 n := by
    apply Summable.sum_le_tsum (s := {3}) (f := conj_term_1 2)
    · intros i hi
      exact conj_term_1_nonneg i
    · exact conj_term_1_summable
  have h_sum_3 : ∑ n ∈ {3}, conj_term_1 2 n = 1 / 43200 := by
    rw [Finset.sum_singleton]
    have hn : 2 < 3 := by norm_num
    rw [conj_term_1_eq 3 hn]
    norm_num
  rw [h_sum_3] at h_le
  calc
    0 < (1 / 43200 : ℝ) := by norm_num
    _ ≤ ∑' n : ℕ, conj_term_1 2 n := h_le

theorem oeis_281820_conjecture_0.disproof : ¬ (type_of% @oeis_281820_conjecture_0) := by
  intro h
  have h2 := h 2 (by omega)
  rcases h2 with ⟨h_eq, _⟩
  have h_eq_16 := tsum_conj_term_2
  have h_zero : 15 * (∑' n : ℕ, conj_term_1 2 n) = 0 := by
    calc
      15 * (∑' n : ℕ, conj_term_1 2 n) = 16 * (∑' n : ℕ, conj_term_1 2 n) - (∑' n : ℕ, conj_term_1 2 n) := by ring
      _ = (∑' n : ℕ, conj_term_2 2 n) - (∑' n : ℕ, conj_term_1 2 n) := by rw [h_eq_16]
      _ = (∑' n : ℕ, conj_term_1 2 n) - (∑' n : ℕ, conj_term_1 2 n) := by rw [← h_eq]
      _ = 0 := by ring
  have h_S_zero : (∑' n : ℕ, conj_term_1 2 n) = 0 := by
    have h15 : (15 : ℝ) ≠ 0 := by norm_num
    exact mul_eq_zero.mp h_zero |>.resolve_left h15
  have h_pos := sum_pos
  rw [h_S_zero] at h_pos
  revert h_pos
  norm_num
