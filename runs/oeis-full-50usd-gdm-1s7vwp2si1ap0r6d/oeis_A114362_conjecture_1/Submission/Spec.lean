import FormalConjectures.Util.ProblemImports


open scoped Nat

open Filter Asymptotics

/--
A114362: Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).

The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.
-/
noncomputable def A114362 (n : ℕ) : ℕ :=
  if h : n = 0 then
    2
  else
    -- Bernoulli numbers B_k are rational numbers.
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    -- Binomial coefficient $\binom{4n}{2n}$ as a rational number.
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))

    -- The rational quantity Q_n = -2 * B_4n / (B_2n^2 * \binom{4n}{2n}).
    -- Note: B_2n is non-zero for n >= 1.
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)

    -- The numerator of the simplified rational, guaranteed to be positive for n >= 1.
    Q_n.num.natAbs

open Complex

-- Helper function for the conjecture, $t(n) = \zeta(2n)/\zeta(n)^2$.
-- We use `Complex.riemannZeta` and take the real part, which is the correct real value for $s > 1$.
noncomputable def A114362_t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

open scoped Real

-- ==========================================
-- Helper lemmas for Riemann Zeta asymptotics
-- ==========================================

lemma term_re (k : ℕ) (n : ℕ) :
    (1 / ((k : ℂ) + 1) ^ (n : ℂ)).re = 1 / (k + 1 : ℝ) ^ n := by
  have h1 : ((k : ℂ) + 1) = ((k + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have h2 : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2]
  have hk1 : 0 ≤ (k : ℝ) + 1 := by positivity
  rw [← ofReal_cpow hk1]
  have h3 : ((k : ℝ) + 1) ^ (n : ℝ) = ((k + 1 : ℝ) ^ n) := by
    rw [Real.rpow_natCast]
  rw [h3]
  have h4 : (1 / (((k + 1 : ℝ) ^ n : ℝ) : ℂ)) = (((1 / (k + 1 : ℝ) ^ n) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h4]
  exact ofReal_re (1 / (k + 1 : ℝ) ^ n)

lemma summable_zeta_re (n : ℕ) (hn : 1 < n) :
    Summable (fun k : ℕ => 1 / (k + 1 : ℝ) ^ n) := by
  have h_rpow : Summable (fun k : ℕ => 1 / |(k : ℝ) + 1| ^ (n : ℝ)) := by
    rw [Real.summable_one_div_nat_add_rpow 1 (n : ℝ)]
    exact_mod_cast hn
  have h_eq : (fun k : ℕ => 1 / (k + 1 : ℝ) ^ n) = (fun k : ℕ => 1 / |(k : ℝ) + 1| ^ (n : ℝ)) := by
    ext k
    have h_pos : 0 ≤ (k : ℝ) + 1 := by positivity
    rw [abs_of_nonneg h_pos, Real.rpow_natCast]
  rw [h_eq]
  exact h_rpow

lemma test_zeta_re (n : ℕ) (hn : 1 < n) :
    (riemannZeta (n : ℂ)).re = ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ n := by
  have h_re : 1 < (n : ℂ).re := by
    push_cast
    exact_mod_cast hn
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h_re]
  have h_sum : Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ (n : ℂ)) := by
    have hf : Summable (fun k : ℕ => 1 / (k : ℂ) ^ (n : ℂ)) := Complex.summable_one_div_nat_cpow.mpr h_re
    have h_add := (summable_nat_add_iff 1 (f := fun k : ℕ => 1 / (k : ℂ) ^ (n : ℂ))).mpr hf
    have h_eq : (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ (n : ℂ)) = (fun k => 1 / ((k + 1 : ℕ) : ℂ) ^ (n : ℂ)) := by
      ext k
      congr 2
      push_cast
      rfl
    rw [h_eq]
    exact h_add
  rw [re_tsum h_sum]
  congr 1
  ext k
  exact term_re k n

lemma split_zeta_re (n : ℕ) (hn : 1 < n) (K : ℕ) :
    (riemannZeta (n : ℂ)).re = (∑ k ∈ Finset.range K, 1 / (k + 1 : ℝ) ^ n) + ∑' k : ℕ, 1 / ((k + K : ℕ) + 1 : ℝ) ^ n := by
  rw [test_zeta_re n hn]
  have h_sum := summable_zeta_re n hn
  have h_add := Summable.sum_add_tsum_nat_add K h_sum
  exact h_add.symm

lemma term_tail_le (K : ℕ) (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    1 / ((k + K : ℕ) + 1 : ℝ) ^ n ≤ ((K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / (K + 1 : ℝ) ^ n) := by
  have hK1 : (0 : ℝ) < (K + 1 : ℝ) := by positivity
  have hD : (0 : ℝ) < ((k + K : ℕ) + 1 : ℝ) := by positivity
  have hDK : (K + 1 : ℝ) ≤ ((k + K : ℕ) + 1 : ℝ) := by
    push_cast
    linarith
  have h_split_D : ((k + K : ℕ) + 1 : ℝ) ^ n = ((k + K : ℕ) + 1 : ℝ) ^ 2 * ((k + K : ℕ) + 1 : ℝ) ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have h_split_K : (K + 1 : ℝ) ^ n = (K + 1 : ℝ) ^ 2 * (K + 1 : ℝ) ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h_split_D, h_split_K]
  have h_RHS : ((K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / ((K + 1 : ℝ) ^ 2 * (K + 1 : ℝ) ^ (n - 2)))
      = 1 / (((k + K : ℕ) + 1 : ℝ) ^ 2 * (K + 1 : ℝ) ^ (n - 2)) := by
    have h_nz_K : (K + 1 : ℝ) ^ 2 ≠ 0 := by positivity
    have h_nz_D : ((k + K : ℕ) + 1 : ℝ) ^ 2 ≠ 0 := by positivity
    have h_nz_K_pow : (K + 1 : ℝ) ^ (n - 2) ≠ 0 := by positivity
    field_simp
  rw [h_RHS]
  rw [one_div, one_div]
  have h_pos_left : 0 < ((k + K : ℕ) + 1 : ℝ) ^ 2 * ((k + K : ℕ) + 1 : ℝ) ^ (n - 2) := by positivity
  have h_pos_right : 0 < ((k + K : ℕ) + 1 : ℝ) ^ 2 * (K + 1 : ℝ) ^ (n - 2) := by positivity
  rw [inv_le_inv₀ h_pos_left h_pos_right]
  gcongr

lemma summable_tail_n (K : ℕ) (n : ℕ) (hn : 1 < n) :
    Summable (fun k : ℕ => 1 / ((k + K : ℕ) + 1 : ℝ) ^ n) := by
  have h_sum := summable_zeta_re n hn
  exact (summable_nat_add_iff K).mpr h_sum

lemma tail_le (K : ℕ) (n : ℕ) (hn : 2 ≤ n) :
    ∑' k : ℕ, 1 / ((k + K : ℕ) + 1 : ℝ) ^ n ≤ (∑' k : ℕ, (K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / (K + 1 : ℝ) ^ n) := by
  have h_sum_left := summable_tail_n K n (by linarith : 1 < n)
  have h_sum_right : Summable (fun k : ℕ => ((K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / (K + 1 : ℝ) ^ n)) := by
    have h2 := summable_tail_n K 2 (by decide)
    have h_sum_mul := Summable.mul_left ((K + 1 : ℝ) ^ 2 * (1 / (K + 1 : ℝ) ^ n)) h2
    have h_eq_term : (fun k : ℕ => ((K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / (K + 1 : ℝ) ^ n))
        = (fun k : ℕ => ((K + 1 : ℝ) ^ 2 * (1 / (K + 1 : ℝ) ^ n)) * (1 / ((k + K : ℕ) + 1 : ℝ) ^ 2)) := by
      ext k
      ring
    rwa [h_eq_term]
  have h_le := Summable.tsum_le_tsum (term_tail_le K n hn) h_sum_left h_sum_right
  have h_RHS_eq : (∑' k : ℕ, ((K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / (K + 1 : ℝ) ^ n))
      = (∑' k : ℕ, (K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2) * (1 / (K + 1 : ℝ) ^ n) := by
    exact tsum_mul_right
  rw [h_RHS_eq] at h_le
  exact h_le

lemma tail_is_O (K : ℕ) :
    (fun n : ℕ => ∑' k : ℕ, 1 / ((k + K : ℕ) + 1 : ℝ) ^ n) =O[atTop] (fun n : ℕ => 1 / (K + 1 : ℝ) ^ n) := by
  let C := ∑' k : ℕ, (K + 1 : ℝ) ^ 2 / ((k + K : ℕ) + 1 : ℝ) ^ 2
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have h_tail_pos : 0 ≤ ∑' k : ℕ, 1 / ((k + K : ℕ) + 1 : ℝ) ^ n := by
    apply tsum_nonneg
    intro k
    positivity
  have h_K_pos : 0 < 1 / (K + 1 : ℝ) ^ n := by positivity
  rw [abs_of_nonneg h_tail_pos, abs_of_pos h_K_pos]
  exact tail_le K n hn

noncomputable def term_fn (a b c d : ℕ) (n : ℕ) : ℝ :=
  ((1:ℝ) / 2^n)^a * ((1:ℝ) / 3^n)^b * ((1:ℝ) / 5^n)^c * ((1:ℝ) / 7^n)^d

lemma term_bound (a b c d : ℕ) (h : 11 ≤ 2^a * 3^b * 5^c * 7^d) (n : ℕ) :
    term_fn a b c d n ≤ 1 / 11^n := by
  dsimp [term_fn]
  have h_eq : ((1:ℝ) / 2^n)^a * ((1:ℝ) / 3^n)^b * ((1:ℝ) / 5^n)^c * ((1:ℝ) / 7^n)^d
      = 1 / ((2^a * 3^b * 5^c * 7^d : ℕ) : ℝ)^n := by
    have h2a : ((2:ℝ)^n)^a = ((2:ℝ)^a)^n := by rw [← pow_mul, mul_comm, pow_mul]
    have h3b : ((3:ℝ)^n)^b = ((3:ℝ)^b)^n := by rw [← pow_mul, mul_comm, pow_mul]
    have h5c : ((5:ℝ)^n)^c = ((5:ℝ)^c)^n := by rw [← pow_mul, mul_comm, pow_mul]
    have h7d : ((7:ℝ)^n)^d = ((7:ℝ)^d)^n := by rw [← pow_mul, mul_comm, pow_mul]
    rw [div_pow, div_pow, div_pow, div_pow]
    simp only [one_pow]
    rw [h2a, h3b, h5c, h7d]
    have h_nz1 : (2:ℝ)^a ≠ 0 := by positivity
    have h_nz2 : (3:ℝ)^b ≠ 0 := by positivity
    have h_nz3 : (5:ℝ)^c ≠ 0 := by positivity
    have h_nz4 : (7:ℝ)^d ≠ 0 := by positivity
    have h_nz_all : ((2^a * 3^b * 5^c * 7^d : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    push_cast
    ring
  rw [h_eq]
  have h_nz_11 : (0:ℝ) < 11^n := by positivity
  have h_nz_base : (0:ℝ) < ((2^a * 3^b * 5^c * 7^d : ℕ) : ℝ)^n := by positivity
  rw [one_div, one_div, inv_le_inv₀ h_nz_base h_nz_11]
  gcongr
  exact_mod_cast h

lemma term_isO (a b c d : ℕ) (h : 11 ≤ 2^a * 3^b * 5^c * 7^d) :
    (fun n : ℕ => term_fn a b c d n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  apply IsBigO.of_bound (1:ℝ)
  filter_upwards [eventually_ge_atTop 0] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have h_term_pos : 0 ≤ term_fn a b c d n := by
    dsimp [term_fn]
    positivity
  have h_11_pos : 0 < (1:ℝ) / 11^n := by positivity
  rw [abs_of_nonneg h_term_pos, abs_of_pos h_11_pos, one_mul]
  exact term_bound a b c d h n

lemma is_O_of_le_const_mul {f g : ℕ → ℝ} (C : ℝ) (hC : 0 ≤ C := by positivity)
    (h : ∀ n, 2 ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (h n hn).trans (mul_le_mul_of_nonneg_left (le_abs_self (g n)) hC)

lemma frac_bound (a b D : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |(b^2 - a) / (b^2 + a) - D| ≤ 1/2 * |b^2 - a - D * (b^2 + a)| := by
  have h_denom : 2 ≤ b^2 + a := by
    have h1 : (1:ℝ) ≤ b^2 := by
      have : (1:ℝ) ≤ b := hb
      nlinarith
    linarith
  have h_denom_pos : 0 < b^2 + a := by linarith
  have h_eq : (b^2 - a) / (b^2 + a) - D = (b^2 - a - D * (b^2 + a)) / (b^2 + a) := by
    have : b^2 + a ≠ 0 := by linarith
    field_simp
  rw [h_eq, abs_div, abs_of_pos h_denom_pos]
  rw [div_eq_mul_one_div]
  rw [mul_comm (1/2)]
  apply mul_le_mul_of_nonneg_left
  · rw [one_div, one_div (2:ℝ)]
    rw [inv_le_inv₀ h_denom_pos (by positivity)]
    linarith
  · positivity

lemma E_bound (B D Ea Eb : ℝ) (hB : 0 ≤ B) (hB2 : B ≤ 2) (hD : 0 ≤ D) (hD1 : D ≤ 1/2) (hEa : 0 ≤ Ea) (hEb : 0 ≤ Eb) (hEb1 : Eb ≤ 1) :
    |2 * B * Eb + Eb^2 - Ea - D * (2 * B * Eb + Eb^2 + Ea)| ≤ 9 * Eb + 2 * Ea := by
  have h_inside : |2 * B * Eb + Eb^2 - Ea - D * (2 * B * Eb + Eb^2 + Ea)| ≤ |2 * B * Eb + Eb^2 - Ea| + |D * (2 * B * Eb + Eb^2 + Ea)| := by
    have h_eq_add : 2 * B * Eb + Eb^2 - Ea - D * (2 * B * Eb + Eb^2 + Ea) = (2 * B * Eb + Eb^2 - Ea) + (- (D * (2 * B * Eb + Eb^2 + Ea))) := by ring
    rw [h_eq_add]
    have h_add := abs_add_le (2 * B * Eb + Eb^2 - Ea) (- (D * (2 * B * Eb + Eb^2 + Ea)))
    rw [abs_neg] at h_add
    exact h_add
  have h_left : |2 * B * Eb + Eb^2 - Ea| ≤ 2 * B * Eb + Eb^2 + Ea := by
    have h_eq_add2 : 2 * B * Eb + Eb^2 - Ea = (2 * B * Eb + Eb^2) + (-Ea) := by ring
    rw [h_eq_add2]
    have h_add2 := abs_add_le (2 * B * Eb + Eb^2) (-Ea)
    rw [abs_neg] at h_add2
    have h_pos_BEb : 0 ≤ 2 * B * Eb + Eb^2 := by positivity
    rw [abs_of_nonneg h_pos_BEb, abs_of_nonneg hEa] at h_add2
    exact h_add2
  have h_right : |D * (2 * B * Eb + Eb^2 + Ea)| ≤ 1/2 * (2 * B * Eb + Eb^2 + Ea) := by
    rw [abs_mul, abs_of_nonneg hD]
    have h_inside_pos : 0 ≤ 2 * B * Eb + Eb^2 + Ea := by positivity
    rw [abs_of_nonneg h_inside_pos]
    apply mul_le_mul_of_nonneg_right hD1 h_inside_pos
  have h_BEb : 2 * B * Eb ≤ 4 * Eb := by
    have : B * Eb ≤ 2 * Eb := by
      apply mul_le_mul_of_nonneg_right hB2 hEb
    linarith
  have h_Eb_sq : Eb^2 ≤ Eb := by
    have : Eb * Eb ≤ Eb * 1 := by
      apply mul_le_mul_of_nonneg_left hEb1 hEb
    linarith
  linarith

lemma zeta_re_ge_one (n : ℕ) (hn : 1 < n) :
    1 ≤ (riemannZeta (n : ℂ)).re := by
  rw [split_zeta_re n hn 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, one_pow, div_one]
  have h_tail_pos : 0 ≤ ∑' k : ℕ, 1 / ((k + 1 : ℕ) + 1 : ℝ) ^ n := by
    apply tsum_nonneg
    intro k
    positivity
  linarith

noncomputable def M_isO_chunk_fn_1 (n : ℕ) : ℝ :=
  ((((-1:ℝ) * term_fn 7 0 0 0 n) + (((-1:ℝ) * term_fn 6 1 0 0 n) + ((-1:ℝ) * term_fn 6 0 1 0 n))) + ((((-1:ℝ) * term_fn 6 0 0 1 n) + ((-1:ℝ) * term_fn 6 0 0 0 n)) + (((-4:ℝ) * term_fn 5 1 0 0 n) + ((-4:ℝ) * term_fn 5 0 1 0 n)))) + (((((-2:ℝ) * term_fn 5 0 0 1 n) + ((-1:ℝ) * term_fn 5 0 0 0 n)) + (((-4:ℝ) * term_fn 4 2 0 0 n) + ((-4:ℝ) * term_fn 4 1 1 0 n))) + ((((-2:ℝ) * term_fn 4 1 0 1 n) + ((-5:ℝ) * term_fn 4 1 0 0 n)) + (((-2:ℝ) * term_fn 4 0 2 0 n) + ((-2:ℝ) * term_fn 4 0 1 1 n))))

lemma M_isO_chunk_isO_1 :
    (fun n : ℕ => M_isO_chunk_fn_1 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((((isBigO_const_mul_self (-1:ℝ) (term_fn 7 0 0 0) atTop).trans (term_isO 7 0 0 0 (by decide))).add (((isBigO_const_mul_self (-1:ℝ) (term_fn 6 1 0 0) atTop).trans (term_isO 6 1 0 0 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 6 0 1 0) atTop).trans (term_isO 6 0 1 0 (by decide))))).add ((((isBigO_const_mul_self (-1:ℝ) (term_fn 6 0 0 1) atTop).trans (term_isO 6 0 0 1 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 6 0 0 0) atTop).trans (term_isO 6 0 0 0 (by decide)))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 5 1 0 0) atTop).trans (term_isO 5 1 0 0 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 5 0 1 0) atTop).trans (term_isO 5 0 1 0 (by decide)))))).add (((((isBigO_const_mul_self (-2:ℝ) (term_fn 5 0 0 1) atTop).trans (term_isO 5 0 0 1 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 5 0 0 0) atTop).trans (term_isO 5 0 0 0 (by decide)))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 4 2 0 0) atTop).trans (term_isO 4 2 0 0 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 4 1 1 0) atTop).trans (term_isO 4 1 1 0 (by decide))))).add ((((isBigO_const_mul_self (-2:ℝ) (term_fn 4 1 0 1) atTop).trans (term_isO 4 1 0 1 (by decide))).add ((isBigO_const_mul_self (-5:ℝ) (term_fn 4 1 0 0) atTop).trans (term_isO 4 1 0 0 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 4 0 2 0) atTop).trans (term_isO 4 0 2 0 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 4 0 1 1) atTop).trans (term_isO 4 0 1 1 (by decide))))))

noncomputable def M_isO_chunk_fn_2 (n : ℕ) : ℝ :=
  ((((-5:ℝ) * term_fn 4 0 1 0 n) + (((-5:ℝ) * term_fn 4 0 0 1 n) + ((-1:ℝ) * term_fn 4 0 0 0 n))) + ((((-2:ℝ) * term_fn 3 3 0 0 n) + ((-2:ℝ) * term_fn 3 2 1 0 n)) + (((-2:ℝ) * term_fn 3 2 0 1 n) + ((-5:ℝ) * term_fn 3 2 0 0 n)))) + (((((-10:ℝ) * term_fn 3 1 1 0 n) + ((-6:ℝ) * term_fn 3 1 0 1 n)) + (((-4:ℝ) * term_fn 3 1 0 0 n) + ((-5:ℝ) * term_fn 3 0 2 0 n))) + ((((-6:ℝ) * term_fn 3 0 1 1 n) + ((-4:ℝ) * term_fn 3 0 1 0 n)) + (((-2:ℝ) * term_fn 3 0 0 2 n) + ((-4:ℝ) * term_fn 3 0 0 1 n))))

lemma M_isO_chunk_isO_2 :
    (fun n : ℕ => M_isO_chunk_fn_2 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((((isBigO_const_mul_self (-5:ℝ) (term_fn 4 0 1 0) atTop).trans (term_isO 4 0 1 0 (by decide))).add (((isBigO_const_mul_self (-5:ℝ) (term_fn 4 0 0 1) atTop).trans (term_isO 4 0 0 1 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 4 0 0 0) atTop).trans (term_isO 4 0 0 0 (by decide))))).add ((((isBigO_const_mul_self (-2:ℝ) (term_fn 3 3 0 0) atTop).trans (term_isO 3 3 0 0 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 3 2 1 0) atTop).trans (term_isO 3 2 1 0 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 3 2 0 1) atTop).trans (term_isO 3 2 0 1 (by decide))).add ((isBigO_const_mul_self (-5:ℝ) (term_fn 3 2 0 0) atTop).trans (term_isO 3 2 0 0 (by decide)))))).add (((((isBigO_const_mul_self (-10:ℝ) (term_fn 3 1 1 0) atTop).trans (term_isO 3 1 1 0 (by decide))).add ((isBigO_const_mul_self (-6:ℝ) (term_fn 3 1 0 1) atTop).trans (term_isO 3 1 0 1 (by decide)))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 3 1 0 0) atTop).trans (term_isO 3 1 0 0 (by decide))).add ((isBigO_const_mul_self (-5:ℝ) (term_fn 3 0 2 0) atTop).trans (term_isO 3 0 2 0 (by decide))))).add ((((isBigO_const_mul_self (-6:ℝ) (term_fn 3 0 1 1) atTop).trans (term_isO 3 0 1 1 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 3 0 1 0) atTop).trans (term_isO 3 0 1 0 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 3 0 0 2) atTop).trans (term_isO 3 0 0 2 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 3 0 0 1) atTop).trans (term_isO 3 0 0 1 (by decide))))))

noncomputable def M_isO_chunk_fn_3 (n : ℕ) : ℝ :=
  ((((-5:ℝ) * term_fn 2 3 0 0 n) + (((-7:ℝ) * term_fn 2 2 1 0 n) + ((-3:ℝ) * term_fn 2 2 0 1 n))) + ((((-5:ℝ) * term_fn 2 2 0 0 n) + ((-3:ℝ) * term_fn 2 1 2 0 n)) + (((-2:ℝ) * term_fn 2 1 1 1 n) + ((-10:ℝ) * term_fn 2 1 1 0 n)))) + (((((-8:ℝ) * term_fn 2 1 0 1 n) + ((-4:ℝ) * term_fn 2 1 0 0 n)) + (((-1:ℝ) * term_fn 2 0 3 0 n) + ((-1:ℝ) * term_fn 2 0 2 1 n))) + ((((-5:ℝ) * term_fn 2 0 2 0 n) + ((-8:ℝ) * term_fn 2 0 1 1 n)) + (((-4:ℝ) * term_fn 2 0 1 0 n) + ((-2:ℝ) * term_fn 2 0 0 2 n))))

lemma M_isO_chunk_isO_3 :
    (fun n : ℕ => M_isO_chunk_fn_3 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((((isBigO_const_mul_self (-5:ℝ) (term_fn 2 3 0 0) atTop).trans (term_isO 2 3 0 0 (by decide))).add (((isBigO_const_mul_self (-7:ℝ) (term_fn 2 2 1 0) atTop).trans (term_isO 2 2 1 0 (by decide))).add ((isBigO_const_mul_self (-3:ℝ) (term_fn 2 2 0 1) atTop).trans (term_isO 2 2 0 1 (by decide))))).add ((((isBigO_const_mul_self (-5:ℝ) (term_fn 2 2 0 0) atTop).trans (term_isO 2 2 0 0 (by decide))).add ((isBigO_const_mul_self (-3:ℝ) (term_fn 2 1 2 0) atTop).trans (term_isO 2 1 2 0 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 2 1 1 1) atTop).trans (term_isO 2 1 1 1 (by decide))).add ((isBigO_const_mul_self (-10:ℝ) (term_fn 2 1 1 0) atTop).trans (term_isO 2 1 1 0 (by decide)))))).add (((((isBigO_const_mul_self (-8:ℝ) (term_fn 2 1 0 1) atTop).trans (term_isO 2 1 0 1 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 2 1 0 0) atTop).trans (term_isO 2 1 0 0 (by decide)))).add (((isBigO_const_mul_self (-1:ℝ) (term_fn 2 0 3 0) atTop).trans (term_isO 2 0 3 0 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 2 0 2 1) atTop).trans (term_isO 2 0 2 1 (by decide))))).add ((((isBigO_const_mul_self (-5:ℝ) (term_fn 2 0 2 0) atTop).trans (term_isO 2 0 2 0 (by decide))).add ((isBigO_const_mul_self (-8:ℝ) (term_fn 2 0 1 1) atTop).trans (term_isO 2 0 1 1 (by decide)))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 2 0 1 0) atTop).trans (term_isO 2 0 1 0 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 2 0 0 2) atTop).trans (term_isO 2 0 0 2 (by decide))))))

noncomputable def M_isO_chunk_fn_4 (n : ℕ) : ℝ :=
  ((((-4:ℝ) * term_fn 2 0 0 1 n) + (((-3:ℝ) * term_fn 1 4 0 0 n) + ((-4:ℝ) * term_fn 1 3 1 0 n))) + ((((-2:ℝ) * term_fn 1 3 0 1 n) + ((-4:ℝ) * term_fn 1 3 0 0 n)) + (((-2:ℝ) * term_fn 1 2 2 0 n) + ((-2:ℝ) * term_fn 1 2 1 1 n)))) + (((((-8:ℝ) * term_fn 1 2 1 0 n) + ((-8:ℝ) * term_fn 1 2 0 1 n)) + (((-4:ℝ) * term_fn 1 2 0 0 n) + ((-6:ℝ) * term_fn 1 1 2 0 n))) + ((((-8:ℝ) * term_fn 1 1 1 1 n) + ((-6:ℝ) * term_fn 1 1 1 0 n)) + (((-2:ℝ) * term_fn 1 1 0 2 n) + ((-6:ℝ) * term_fn 1 1 0 1 n))))

lemma M_isO_chunk_isO_4 :
    (fun n : ℕ => M_isO_chunk_fn_4 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((((isBigO_const_mul_self (-4:ℝ) (term_fn 2 0 0 1) atTop).trans (term_isO 2 0 0 1 (by decide))).add (((isBigO_const_mul_self (-3:ℝ) (term_fn 1 4 0 0) atTop).trans (term_isO 1 4 0 0 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 1 3 1 0) atTop).trans (term_isO 1 3 1 0 (by decide))))).add ((((isBigO_const_mul_self (-2:ℝ) (term_fn 1 3 0 1) atTop).trans (term_isO 1 3 0 1 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 1 3 0 0) atTop).trans (term_isO 1 3 0 0 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 1 2 2 0) atTop).trans (term_isO 1 2 2 0 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 1 2 1 1) atTop).trans (term_isO 1 2 1 1 (by decide)))))).add (((((isBigO_const_mul_self (-8:ℝ) (term_fn 1 2 1 0) atTop).trans (term_isO 1 2 1 0 (by decide))).add ((isBigO_const_mul_self (-8:ℝ) (term_fn 1 2 0 1) atTop).trans (term_isO 1 2 0 1 (by decide)))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 1 2 0 0) atTop).trans (term_isO 1 2 0 0 (by decide))).add ((isBigO_const_mul_self (-6:ℝ) (term_fn 1 1 2 0) atTop).trans (term_isO 1 1 2 0 (by decide))))).add ((((isBigO_const_mul_self (-8:ℝ) (term_fn 1 1 1 1) atTop).trans (term_isO 1 1 1 1 (by decide))).add ((isBigO_const_mul_self (-6:ℝ) (term_fn 1 1 1 0) atTop).trans (term_isO 1 1 1 0 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 1 1 0 2) atTop).trans (term_isO 1 1 0 2 (by decide))).add ((isBigO_const_mul_self (-6:ℝ) (term_fn 1 1 0 1) atTop).trans (term_isO 1 1 0 1 (by decide))))))

noncomputable def M_isO_chunk_fn_5 (n : ℕ) : ℝ :=
  ((((-2:ℝ) * term_fn 1 0 3 0 n) + (((-4:ℝ) * term_fn 1 0 2 1 n) + ((-3:ℝ) * term_fn 1 0 2 0 n))) + ((((-2:ℝ) * term_fn 1 0 1 2 n) + ((-6:ℝ) * term_fn 1 0 1 1 n)) + (((-3:ℝ) * term_fn 1 0 0 2 n) + ((-2:ℝ) * term_fn 1 0 0 1 n)))) + (((((-1:ℝ) * term_fn 0 5 0 0 n) + ((-1:ℝ) * term_fn 0 4 1 0 n)) + (((-1:ℝ) * term_fn 0 4 0 1 n) + ((-1:ℝ) * term_fn 0 4 0 0 n))) + ((((-4:ℝ) * term_fn 0 3 1 0 n) + ((-4:ℝ) * term_fn 0 3 0 1 n)) + (((-2:ℝ) * term_fn 0 3 0 0 n) + ((-2:ℝ) * term_fn 0 2 2 0 n))))

lemma M_isO_chunk_isO_5 :
    (fun n : ℕ => M_isO_chunk_fn_5 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((((isBigO_const_mul_self (-2:ℝ) (term_fn 1 0 3 0) atTop).trans (term_isO 1 0 3 0 (by decide))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 1 0 2 1) atTop).trans (term_isO 1 0 2 1 (by decide))).add ((isBigO_const_mul_self (-3:ℝ) (term_fn 1 0 2 0) atTop).trans (term_isO 1 0 2 0 (by decide))))).add ((((isBigO_const_mul_self (-2:ℝ) (term_fn 1 0 1 2) atTop).trans (term_isO 1 0 1 2 (by decide))).add ((isBigO_const_mul_self (-6:ℝ) (term_fn 1 0 1 1) atTop).trans (term_isO 1 0 1 1 (by decide)))).add (((isBigO_const_mul_self (-3:ℝ) (term_fn 1 0 0 2) atTop).trans (term_isO 1 0 0 2 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 1 0 0 1) atTop).trans (term_isO 1 0 0 1 (by decide)))))).add (((((isBigO_const_mul_self (-1:ℝ) (term_fn 0 5 0 0) atTop).trans (term_isO 0 5 0 0 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 0 4 1 0) atTop).trans (term_isO 0 4 1 0 (by decide)))).add (((isBigO_const_mul_self (-1:ℝ) (term_fn 0 4 0 1) atTop).trans (term_isO 0 4 0 1 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 0 4 0 0) atTop).trans (term_isO 0 4 0 0 (by decide))))).add ((((isBigO_const_mul_self (-4:ℝ) (term_fn 0 3 1 0) atTop).trans (term_isO 0 3 1 0 (by decide))).add ((isBigO_const_mul_self (-4:ℝ) (term_fn 0 3 0 1) atTop).trans (term_isO 0 3 0 1 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 0 3 0 0) atTop).trans (term_isO 0 3 0 0 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 0 2 2 0) atTop).trans (term_isO 0 2 2 0 (by decide))))))

noncomputable def M_isO_chunk_fn_6 (n : ℕ) : ℝ :=
  ((((-4:ℝ) * term_fn 0 2 1 1 n) + (((-4:ℝ) * term_fn 0 2 1 0 n) + ((-2:ℝ) * term_fn 0 2 0 2 n))) + ((((-4:ℝ) * term_fn 0 2 0 1 n) + ((-3:ℝ) * term_fn 0 1 2 0 n)) + (((-6:ℝ) * term_fn 0 1 1 1 n) + ((-2:ℝ) * term_fn 0 1 1 0 n)))) + (((((-3:ℝ) * term_fn 0 1 0 2 n) + ((-2:ℝ) * term_fn 0 1 0 1 n)) + (((-1:ℝ) * term_fn 0 0 3 0 n) + ((-3:ℝ) * term_fn 0 0 2 1 n))) + ((((-1:ℝ) * term_fn 0 0 2 0 n) + ((-3:ℝ) * term_fn 0 0 1 2 n)) + (((-2:ℝ) * term_fn 0 0 1 1 n) + ((-1:ℝ) * term_fn 0 0 0 3 n))))

lemma M_isO_chunk_isO_6 :
    (fun n : ℕ => M_isO_chunk_fn_6 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((((isBigO_const_mul_self (-4:ℝ) (term_fn 0 2 1 1) atTop).trans (term_isO 0 2 1 1 (by decide))).add (((isBigO_const_mul_self (-4:ℝ) (term_fn 0 2 1 0) atTop).trans (term_isO 0 2 1 0 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 0 2 0 2) atTop).trans (term_isO 0 2 0 2 (by decide))))).add ((((isBigO_const_mul_self (-4:ℝ) (term_fn 0 2 0 1) atTop).trans (term_isO 0 2 0 1 (by decide))).add ((isBigO_const_mul_self (-3:ℝ) (term_fn 0 1 2 0) atTop).trans (term_isO 0 1 2 0 (by decide)))).add (((isBigO_const_mul_self (-6:ℝ) (term_fn 0 1 1 1) atTop).trans (term_isO 0 1 1 1 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 0 1 1 0) atTop).trans (term_isO 0 1 1 0 (by decide)))))).add (((((isBigO_const_mul_self (-3:ℝ) (term_fn 0 1 0 2) atTop).trans (term_isO 0 1 0 2 (by decide))).add ((isBigO_const_mul_self (-2:ℝ) (term_fn 0 1 0 1) atTop).trans (term_isO 0 1 0 1 (by decide)))).add (((isBigO_const_mul_self (-1:ℝ) (term_fn 0 0 3 0) atTop).trans (term_isO 0 0 3 0 (by decide))).add ((isBigO_const_mul_self (-3:ℝ) (term_fn 0 0 2 1) atTop).trans (term_isO 0 0 2 1 (by decide))))).add ((((isBigO_const_mul_self (-1:ℝ) (term_fn 0 0 2 0) atTop).trans (term_isO 0 0 2 0 (by decide))).add ((isBigO_const_mul_self (-3:ℝ) (term_fn 0 0 1 2) atTop).trans (term_isO 0 0 1 2 (by decide)))).add (((isBigO_const_mul_self (-2:ℝ) (term_fn 0 0 1 1) atTop).trans (term_isO 0 0 1 1 (by decide))).add ((isBigO_const_mul_self (-1:ℝ) (term_fn 0 0 0 3) atTop).trans (term_isO 0 0 0 3 (by decide))))))

noncomputable def M_isO_chunk_fn_7 (n : ℕ) : ℝ :=
  ((-1:ℝ) * term_fn 0 0 0 2 n)

lemma M_isO_chunk_isO_7 :
    (fun n : ℕ => M_isO_chunk_fn_7 n) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  exact ((isBigO_const_mul_self (-1:ℝ) (term_fn 0 0 0 2) atTop).trans (term_isO 0 0 0 2 (by decide)))

lemma M_isO :
    (fun n : ℕ =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) =O[atTop] (fun n : ℕ => (1:ℝ) / 11^n) := by
  have h_eq : (fun n : ℕ =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) = (fun n : ℕ => ((M_isO_chunk_fn_1 n) + ((M_isO_chunk_fn_2 n) + (M_isO_chunk_fn_3 n))) + (((M_isO_chunk_fn_4 n) + (M_isO_chunk_fn_5 n)) + ((M_isO_chunk_fn_6 n) + (M_isO_chunk_fn_7 n)))) := by
    ext n
    simp only
    dsimp [M_isO_chunk_fn_1, M_isO_chunk_fn_2, M_isO_chunk_fn_3, M_isO_chunk_fn_4, M_isO_chunk_fn_5, M_isO_chunk_fn_6, M_isO_chunk_fn_7, term_fn]
    ring
  rw [h_eq]
  exact (M_isO_chunk_isO_1.add (M_isO_chunk_isO_2.add M_isO_chunk_isO_3)).add ((M_isO_chunk_isO_4.add M_isO_chunk_isO_5).add (M_isO_chunk_isO_6.add M_isO_chunk_isO_7))

-- ==========================================
-- E_isO Lemma
-- ==========================================

lemma h_tele_sum : (∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) = 1 := by
  have h_nonneg : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
    intro k
    have h1 : 0 < (k : ℝ) + 1 := by positivity
    have h2 : 0 < (k : ℝ) + 2 := by positivity
    have h3 : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
    have h4 : 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) := by
      rw [one_div, one_div]
      exact (inv_le_inv₀ h2 h1).mpr h3
    linarith
  have h_hasSum : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg h_nonneg]
    have h_sum_eq : (fun n : ℕ => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))) = (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) := by
      ext n
      induction' n with n ih
      · simp
      · rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    rw [h_sum_eq]
    have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := Filter.Tendsto.sub h1 h2
    rw [sub_zero] at h3
    exact h3
  exact h_hasSum.tsum_eq

lemma h_tele_le : ∑' k : ℕ, 1 / (k + 2 : ℝ) ^ 2 ≤ 1 := by
  have h_sum_tail := (summable_nat_add_iff 1).mpr (summable_zeta_re 2 (by norm_num))
  have h_eq_tail : ∀ n : ℕ, 1 / (↑(n + 1) + 1 : ℝ) ^ 2 = 1 / (↑n + 2 : ℝ) ^ 2 := by
    intro n; congr 2; push_cast; ring
  have h_sum_tail2 : Summable (fun k : ℕ => 1 / (k + 2 : ℝ) ^ 2) := Summable.congr h_sum_tail h_eq_tail
  have h_sum_tele : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
    have h_eq_tele : (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) = (fun k : ℕ => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
      ext k
      field_simp
      ring
    rw [h_eq_tele]
    apply Summable.of_nonneg_of_le (fun k => by positivity) _ (summable_zeta_re 2 (by norm_num))
    intro k
    have h_mul_le : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      nlinarith
    rw [one_div, one_div]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact h_mul_le
  have h_tsum_le : (∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2) ≤ ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
    apply Summable.tsum_le_tsum
    · intro k
      have h_nz1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h_nz2 : ((k : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      nlinarith
    · exact h_sum_tail2
    · exact h_sum_tele
  rw [h_tele_sum] at h_tsum_le
  exact h_tsum_le

lemma h_zeta2_le_2 : ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2 ≤ 2 := by
  have h_split_zeta : ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2 = 1 + ∑' k : ℕ, 1 / (k + 2 : ℝ) ^ 2 := by
    have h_sum_zeta2 := summable_zeta_re 2 (by norm_num)
    have h_add := Summable.sum_add_tsum_nat_add 1 h_sum_zeta2
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, one_pow, div_one] at h_add
    have h_eq : (fun i : ℕ => 1 / (↑(i + 1) + 1 : ℝ) ^ 2) = (fun k : ℕ => 1 / (k + 2 : ℝ) ^ 2) := by
      ext i; congr 2; push_cast; ring
    rw [h_eq] at h_add
    exact h_add.symm
  rw [h_split_zeta]
  have h_le := h_tele_le
  linarith

lemma h_Eb_le_tail2_lemma (n : ℕ) (hn : 2 ≤ n) :
    ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n ≤ (∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) - 1 := by
  have h_sum_Eb := summable_tail_n 10 n (by linarith : 1 < n)
  have h_sum_tail2 : Summable (fun k : ℕ => 1 / (k + 2 : ℝ) ^ 2) := by
    have h_sh := summable_zeta_re 2 (by norm_num)
    have h_sh2 := (summable_nat_add_iff 1).mpr h_sh
    have h_eq : (fun n : ℕ => 1 / (↑(n + 1) + 1 : ℝ) ^ 2) = (fun k : ℕ => 1 / (↑k + 2 : ℝ) ^ 2) := by
      ext n; congr 2; push_cast; ring
    rwa [h_eq] at h_sh2
  have h_le_tail : ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n ≤ ∑' k : ℕ, 1 / (k + 2 : ℝ) ^ 2 := by
    apply Summable.tsum_le_tsum _ h_sum_Eb h_sum_tail2
    intro k
    have h_base2 : (k + 2 : ℝ) ≤ ((k + 10 : ℕ) + 1 : ℝ) := by
      push_cast
      linarith
    have h_pow2 : (k + 2 : ℝ) ^ 2 ≤ ((k + 10 : ℕ) + 1 : ℝ) ^ n := by
      apply le_trans (b := ((k + 10 : ℕ) + 1 : ℝ) ^ 2)
      · exact pow_le_pow_left₀ (by positivity) h_base2 2
      · exact pow_le_pow_right₀ (by push_cast; linarith) hn
    rw [one_div, one_div]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact h_pow2
  have h_split_zeta : ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2 = 1 + ∑' k : ℕ, 1 / (k + 2 : ℝ) ^ 2 := by
    have h_sum_zeta2 := summable_zeta_re 2 (by norm_num)
    have h_add := Summable.sum_add_tsum_nat_add 1 h_sum_zeta2
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, one_pow, div_one] at h_add
    have h_eq : (fun i : ℕ => 1 / (↑(i + 1) + 1 : ℝ) ^ 2) = (fun k : ℕ => 1 / (k + 2 : ℝ) ^ 2) := by
      ext i; congr 2; push_cast; ring
    rw [h_eq] at h_add
    exact h_add.symm
  linarith

lemma E_isO :
    (fun n : ℕ =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n);
      let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n;
      2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  have h_C_pos : 0 ≤ 9 * (∑' k : ℕ, (10 + 1 : ℝ) ^ 2 / ((k + 10 : ℕ) + 1 : ℝ) ^ 2) + 2 * (∑' k : ℕ, (3 + 1 : ℝ) ^ 2 / ((k + 3 : ℕ) + 1 : ℝ) ^ 2) := by
    apply add_nonneg
    · apply mul_nonneg (by norm_num)
      apply tsum_nonneg
      intro k
      positivity
    · apply mul_nonneg (by norm_num)
      apply tsum_nonneg
      intro k
      positivity
  refine is_O_of_le_const_mul (9 * (∑' k : ℕ, (10 + 1 : ℝ) ^ 2 / ((k + 10 : ℕ) + 1 : ℝ) ^ 2) + 2 * (∑' k : ℕ, (3 + 1 : ℝ) ^ 2 / ((k + 3 : ℕ) + 1 : ℝ) ^ 2)) h_C_pos ?_
  intro n hn
  let x2 := (1:ℝ) / 2^n
  let x3 := (1:ℝ) / 3^n
  let x4 := (1:ℝ) / 4^n
  let x5 := (1:ℝ) / 5^n
  let x6 := (1:ℝ) / 6^n
  let x7 := (1:ℝ) / 7^n;
  let x8 := (1:ℝ) / 8^n
  let x9 := (1:ℝ) / 9^n
  let x10 := (1:ℝ) / 10^n
  let D := x2 + x3 + x5 + x7;
  let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n)
  let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n
  let B := 1 + x2 + x3 + (x2)^2 + x5 + x2 * x3 + x7 + (x2)^3 + (x3)^2 + x2 * x5
  let E := 2 * B * Eb + Eb^2 - Ea - D * (2 * B * Eb + Eb^2 + Ea)

  have hB0 : 0 ≤ B := by positivity
  have hB2 : B ≤ 2 := by
    have h_x2 : x2 ≤ 1/4 := by
      dsimp [x2]
      rw [one_div, one_div (4:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (4 : ℝ) = 2^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have h_x3 : x3 ≤ 1/9 := by
      dsimp [x3]
      rw [one_div, one_div (9:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (9 : ℝ) = 3^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have h_x5 : x5 ≤ 1/25 := by
      dsimp [x5]
      rw [one_div, one_div (25:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (25 : ℝ) = 5^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have h_x7 : x7 ≤ 1/49 := by
      dsimp [x7]
      rw [one_div, one_div (49:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (49 : ℝ) = 7^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have hx2_pos : 0 ≤ x2 := by positivity
    have hx3_pos : 0 ≤ x3 := by positivity
    have hx5_pos : 0 ≤ x5 := by positivity
    have h_x2_sq : x2^2 ≤ 1/16 := by nlinarith
    have h_x2_x3 : x2 * x3 ≤ 1/36 := by nlinarith
    have h_x2_cube : x2^3 ≤ 1/64 := by
      have : x2^3 = x2 * x2^2 := by ring
      rw [this]
      nlinarith
    have h_x3_sq : x3^2 ≤ 1/81 := by nlinarith
    have h_x2_x5 : x2 * x5 ≤ 1/100 := by nlinarith
    linarith
  have hD0 : 0 ≤ D := by positivity
  have hD2 : D ≤ 1/2 := by
    have h_x2 : x2 ≤ 1/4 := by
      dsimp [x2]
      rw [one_div, one_div (4:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (4 : ℝ) = 2^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have h_x3 : x3 ≤ 1/9 := by
      dsimp [x3]
      rw [one_div, one_div (9:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (9 : ℝ) = 3^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have h_x5 : x5 ≤ 1/25 := by
      dsimp [x5]
      rw [one_div, one_div (25:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (25 : ℝ) = 5^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    have h_x7 : x7 ≤ 1/49 := by
      dsimp [x7]
      rw [one_div, one_div (49:ℝ)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (49 : ℝ) = 7^2 := by norm_num
      rw [this]
      gcongr
      norm_num
    linarith
  have hEa0 : 0 ≤ Ea := by
    apply tsum_nonneg
    intro k
    positivity
  have hEb0 : 0 ≤ Eb := by
    apply tsum_nonneg
    intro k
    positivity
  have hEb1 : Eb ≤ 1 := by
    have h_Eb_le_tail2 : Eb ≤ (∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) - 1 := h_Eb_le_tail2_lemma n hn
    have h_zeta2_le_2 := h_zeta2_le_2
    linarith
  have hE_le := E_bound B D Ea Eb hB0 hB2 hD0 hD2 hEa0 hEb0 hEb1

  have h_Eb_le : Eb ≤ (∑' k : ℕ, (10 + 1 : ℝ) ^ 2 / ((k + 10 : ℕ) + 1 : ℝ) ^ 2) * (1 / 11^n) := by
    have h_le := tail_le 10 n hn
    have h_11 : ((10 : ℕ) : ℝ) + 1 = 11 := by norm_num
    rw [h_11] at h_le
    have h_10_1 : (10 : ℝ) + 1 = 11 := by norm_num
    rw [h_10_1]
    exact h_le
  have h_Ea_le : Ea ≤ (∑' k : ℕ, (3 + 1 : ℝ) ^ 2 / ((k + 3 : ℕ) + 1 : ℝ) ^ 2) * (1 / 11^n) := by
    have h_le_16 := tail_le 3 (2 * n) (by linarith : 2 ≤ 2 * n)
    have h_16_11 : 1 / (16 : ℝ) ^ n ≤ 1 / 11^n := by
      rw [one_div, one_div]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      gcongr
      norm_num
    have h_3_1 : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
    rw [h_3_1] at h_le_16
    have h_4_2n : (4 : ℝ) ^ (2 * n) = 16^n := by
      rw [pow_mul]
      norm_num
    rw [h_4_2n] at h_le_16
    apply le_trans h_le_16
    have h_3_1_goal : (3 : ℝ) + 1 = 4 := by norm_num
    rw [h_3_1_goal]
    apply mul_le_mul_of_nonneg_left h_16_11
    apply tsum_nonneg
    intro k
    positivity

  have h_E_bound_O : 9 * Eb + 2 * Ea ≤ (9 * (∑' k : ℕ, (10 + 1 : ℝ) ^ 2 / ((k + 10 : ℕ) + 1 : ℝ) ^ 2) + 2 * (∑' k : ℕ, (3 + 1 : ℝ) ^ 2 / ((k + 3 : ℕ) + 1 : ℝ) ^ 2)) * (1 / 11^n) := by
    linarith [h_Eb_le, h_Ea_le]
  have h_E_O : |E| ≤ (9 * (∑' k : ℕ, (10 + 1 : ℝ) ^ 2 / ((k + 10 : ℕ) + 1 : ℝ) ^ 2) + 2 * (∑' k : ℕ, (3 + 1 : ℝ) ^ 2 / ((k + 3 : ℕ) + 1 : ℝ) ^ 2)) * (1 / 11^n) := by
    exact le_trans hE_le h_E_bound_O

  exact h_E_O

-- ==========================================
-- Main Conjecture Proof
-- ==========================================

theorem oeis_A114362_conjecture_1 :
    (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  have h_F_le : (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1/2 * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) n| + 1/2 * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n);
      let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n;
      2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) n|) := by
    refine is_O_of_le_const_mul 1 (by norm_num) ?_
    intro n hn
    rw [one_mul]
    let x2 := (1:ℝ) / 2^n
    let x3 := (1:ℝ) / 3^n
    let x4 := (1:ℝ) / 4^n
    let x5 := (1:ℝ) / 5^n
    let x6 := (1:ℝ) / 6^n
    let x7 := (1:ℝ) / 7^n;
    let x8 := (1:ℝ) / 8^n
    let x9 := (1:ℝ) / 9^n
    let x10 := (1:ℝ) / 10^n
    let a := (riemannZeta (2 * (n : ℂ))).re
    let b := (riemannZeta (n : ℂ)).re
    let D := x2 + x3 + x5 + x7;
    let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n)
    let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n
    let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10
    let A := 1 + x4 + x9
    let M := B^2 * (1 - D) - A * (1 + D)
    let E := 2 * B * Eb + Eb^2 - Ea - D * (2 * B * Eb + Eb^2 + Ea)

    have h_a_eq : (riemannZeta (2 * (n : ℂ))).re = 1 + x4 + x9 + Ea := by
      have h_a_cast : (riemannZeta (2 * (n : ℂ))).re = (riemannZeta ((2 * n : ℕ) : ℂ)).re := by
        congr 2
        push_cast
        ring
      rw [h_a_cast]
      rw [split_zeta_re (2 * n) (by linarith : 1 < 2 * n) 3]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, zero_add, one_pow, div_one, Nat.cast_one,
        Nat.cast_ofNat, Nat.cast_add]
      have h_eq_Ea : (∑' k : ℕ, 1 / (↑k + 3 + 1 : ℝ) ^ (2 * n)) = Ea := by
        dsimp [Ea]
        congr 1
        ext k
        congr 2
        push_cast
        ring
      rw [h_eq_Ea]
      have h_add2 : (1 + 1 : ℝ) = 2 := by norm_num
      have h_add3 : (2 + 1 : ℝ) = 3 := by norm_num
      rw [h_add2, h_add3]
      have h_pow_mul2 : (2 : ℝ) ^ (2 * n) = 4^n := by
        rw [pow_mul]
        norm_num
      have h_pow_mul3 : (3 : ℝ) ^ (2 * n) = 9^n := by
        rw [pow_mul]
        norm_num
      rw [h_pow_mul2, h_pow_mul3]
    have h_b_eq : (riemannZeta (n : ℂ)).re = 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + Eb := by
      rw [split_zeta_re n (by linarith : 1 < n) 10]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, zero_add, one_pow, div_one, Nat.cast_one,
        Nat.cast_ofNat, Nat.cast_add]
      have h_eq_Eb : (∑' k : ℕ, 1 / (↑k + 10 + 1 : ℝ) ^ n) = Eb := by
        dsimp [Eb]
        congr 1
        ext k
        congr 2
        push_cast
        ring
      rw [h_eq_Eb]
      have h_add2 : (1 + 1 : ℝ) = 2 := by norm_num
      have h_add3 : (2 + 1 : ℝ) = 3 := by norm_num
      have h_add4 : (3 + 1 : ℝ) = 4 := by norm_num
      have h_add5 : (4 + 1 : ℝ) = 5 := by norm_num
      have h_add6 : (5 + 1 : ℝ) = 6 := by norm_num
      have h_add7 : (6 + 1 : ℝ) = 7 := by norm_num
      have h_add8 : (7 + 1 : ℝ) = 8 := by norm_num
      have h_add9 : (8 + 1 : ℝ) = 9 := by norm_num
      have h_add10 : (9 + 1 : ℝ) = 10 := by norm_num
      rw [h_add2, h_add3, h_add4, h_add5, h_add6, h_add7, h_add8, h_add9, h_add10]
    have h_t_eq : A114362_t n = a / b^2 := by
      rw [A114362_t]
    have h_F_eq : (1 - A114362_t n) / (1 + A114362_t n) - (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n)
        = (b^2 - a) / (b^2 + a) - D := by
      rw [h_t_eq]
      have h_nz_b : b ≠ 0 := by
        have : 1 ≤ b := zeta_re_ge_one n (by linarith)
        linarith
      have h_eq_frac : (1 - a / b^2) / (1 + a / b^2) = (b^2 - a) / (b^2 + a) := by
        field_simp
      rw [h_eq_frac]
    rw [h_F_eq]
    have ha_ge_one : 1 ≤ a := by
      have h_a_cast : a = (riemannZeta ((2 * n : ℕ) : ℂ)).re := by
        congr 2
        push_cast
        ring
      rw [h_a_cast]
      exact zeta_re_ge_one (2 * n) (by linarith)
    have hb_ge_one : 1 ≤ b := zeta_re_ge_one n (by linarith)
    have h_frac := frac_bound a b D ha_ge_one hb_ge_one
    apply le_trans h_frac
    have h_b2_a_eq : b^2 - a - D * (b^2 + a) = M + E := by
      change (riemannZeta (n : ℂ)).re^2 - (riemannZeta (2 * (n : ℂ))).re - D * ((riemannZeta (n : ℂ)).re^2 + (riemannZeta (2 * (n : ℂ))).re) = M + E
      rw [h_b_eq, h_a_eq]
      ring
    rw [h_b2_a_eq]
    have h_x4 : x4 = x2^2 := by
      dsimp [x4, x2]
      rw [one_div_pow]
      congr 1
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h_x6 : x6 = x2 * x3 := by
      dsimp [x6, x2, x3]
      rw [one_div_mul_one_div]
      congr 1
      rw [← mul_pow]
      norm_num
    have h_x8 : x8 = x2^3 := by
      dsimp [x8, x2]
      rw [one_div_pow]
      congr 1
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h_x9 : x9 = x3^2 := by
      dsimp [x9, x3]
      rw [one_div_pow]
      congr 1
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h_x10 : x10 = x2 * x5 := by
      dsimp [x10, x2, x5]
      rw [one_div_mul_one_div]
      congr 1
      rw [← mul_pow]
      norm_num
    have h_frac_mul : 1/2 * |M + E| ≤ 1/2 * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) n| + 1/2 * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n);
      let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n;
      2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) n| := by
      change 1/2 * |((1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10)^2 * (1 - D) - (1 + x4 + x9) * (1 + D)) + (2 * (1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * Eb + Eb^2 - Ea - D * (2 * (1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * Eb + Eb^2 + Ea))| ≤
        1/2 * |(fun n =>
          let x2 := (1:ℝ) / 2^n
          let x3 := (1:ℝ) / 3^n
          let x5 := (1:ℝ) / 5^n
          let x7 := (1:ℝ) / 7^n;
          let x4 := x2^2
          let x6 := x2*x3
          let x8 := x2^3
          let x9 := x3^2
          let x10 := x2*x5
          let A := 1 + x4 + x9
          let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10
          let D := x2 + x3 + x5 + x7;
          B^2 * (1 - D) - A * (1 + D)) n| + 1/2 * |(fun n =>
          let x2 := (1:ℝ) / 2^n
          let x3 := (1:ℝ) / 3^n
          let x5 := (1:ℝ) / 5^n
          let x7 := (1:ℝ) / 7^n;
          let x4 := x2^2
          let x6 := x2*x3
          let x8 := x2^3
          let x9 := x3^2
          let x10 := x2*x5
          let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10
          let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n)
          let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n
          2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) n|
      dsimp only
      rw [h_x4, h_x6, h_x8, h_x9, h_x10]
      have h_tri := abs_add_le ((1 + x2 + x3 + x2^2 + x5 + x2 * x3 + x7 + x2^3 + x3^2 + x2 * x5)^2 * (1 - D) - (1 + x2^2 + x3^2) * (1 + D)) (2 * (1 + x2 + x3 + x2^2 + x5 + x2 * x3 + x7 + x2^3 + x3^2 + x2 * x5) * Eb + Eb^2 - Ea - D * (2 * (1 + x2 + x3 + x2^2 + x5 + x2 * x3 + x7 + x2^3 + x3^2 + x2 * x5) * Eb + Eb^2 + Ea))
      linarith
    exact h_frac_mul

  have h_M_abs_isO : (fun n : ℕ => |(fun n : ℕ =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) n|) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
    have h_rewritten := isBigO_iff.1 M_isO
    rw [isBigO_iff]
    rcases h_rewritten with ⟨c, hc⟩
    use c
    filter_upwards [hc] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn ⊢
    rw [abs_abs]
    exact hn

  have h_E_abs_isO : (fun n : ℕ => |(fun n : ℕ =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n);
      let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n;
      2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) n|) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
    have h_rewritten := isBigO_iff.1 E_isO
    rw [isBigO_iff]
    rcases h_rewritten with ⟨c, hc⟩
    use c
    filter_upwards [hc] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn ⊢
    rw [abs_abs]
    exact hn

  have h_sum_isO : (fun n : ℕ => 1/2 * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) n| + 1/2 * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n);
      let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n;
      2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) n|) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
    have h1 : (fun n : ℕ => (1/2:ℝ) * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let A := 1 + x4 + x9;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let D := x2 + x3 + x5 + x7;
      B^2 * (1 - D) - A * (1 + D)) n|) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := h_M_abs_isO.const_mul_left (1/2)
    have h2 : (fun n : ℕ => (1/2:ℝ) * |(fun n =>
      let x2 := (1:ℝ) / 2^n;
      let x3 := (1:ℝ) / 3^n;
      let x5 := (1:ℝ) / 5^n;
      let x7 := (1:ℝ) / 7^n;
      let x4 := x2^2;
      let x6 := x2*x3;
      let x8 := x2^3;
      let x9 := x3^2;
      let x10 := x2*x5;
      let B := 1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10;
      let Ea := ∑' k : ℕ, 1 / ((k + 3 : ℕ) + 1 : ℝ) ^ (2 * n);
      let Eb := ∑' k : ℕ, 1 / ((k + 10 : ℕ) + 1 : ℝ) ^ n;
      2 * B * Eb + Eb^2 - Ea - (x2 + x3 + x5 + x7) * (2 * B * Eb + Eb^2 + Ea)) n|) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := h_E_abs_isO.const_mul_left (1/2)
    exact h1.add h2

  exact h_F_le.trans h_sum_isO
