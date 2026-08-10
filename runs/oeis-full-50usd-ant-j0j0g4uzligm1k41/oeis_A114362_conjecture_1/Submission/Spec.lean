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

/--
A114362 Conjecture: (1 - t(n))/(1 + t(n)) = 1/2^n + 1/3^n + 1/5^n + 1/7^n + O(1/11^n),
where t(n) = zeta(2n)/zeta(n)^2. Cf. A348829.
This is formalized as the difference between the LHS and the sum of the first four inverse prime powers
being $O(1/11^n)$ as $n \to \infty$.
-/

theorem zeta_re_eq (n : ℕ) (hn : 1 < n) :
    (riemannZeta (n : ℂ)).re = ∑' k : ℕ, 1 / (k : ℝ) ^ n := by
  have h1 : riemannZeta (n : ℂ) = ∑' k : ℕ, 1 / (k : ℂ) ^ n :=
    zeta_nat_eq_tsum_of_gt_one hn
  have h2 : (∑' k : ℕ, 1 / (k : ℂ) ^ n) = ((∑' k : ℕ, 1 / (k : ℝ) ^ n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    ext k
    push_cast
    ring
  rw [h1, h2, Complex.ofReal_re]

theorem zeta_re_eq2 (n : ℕ) (hn : 1 ≤ n) :
    (riemannZeta (2 * (n : ℂ))).re = ∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n) := by
  have h2n : (2 : ℂ) * (n : ℂ) = ((2 * n : ℕ) : ℂ) := by push_cast; ring
  rw [h2n]
  exact zeta_re_eq (2 * n) (by omega)

/-- Summability of `1/(k:ℝ)^p` for `p ≥ 2`, shifted by `m`. -/
theorem summable_shift (p m : ℕ) (hp : 2 ≤ p) :
    Summable (fun k : ℕ => 1 / ((k + m : ℕ) : ℝ) ^ p) :=
  (summable_nat_add_iff m).mpr (Real.summable_one_div_nat_pow.mpr hp)

/-- The whole 2-series sum is at most `2`. -/
theorem tsum_inv_sq_le : (∑' k : ℕ, 1 / (k : ℝ) ^ 2) ≤ 2 := by
  rw [hasSum_zeta_two.tsum_eq]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith [Real.pi_pos, hpi]

/-- Shifted 2-series tail is at most `2`. -/
theorem tail2_le (m : ℕ) : (∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hsum : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (le_refl 2)
  have hsplit := hsum.sum_add_tsum_nat_add m
  have hnonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.range m, 1 / (i : ℝ) ^ 2 := by
    apply Finset.sum_nonneg; intro i _; positivity
  have : (∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ 2) ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := by
    have : (∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ 2) = (∑' k : ℕ, 1 / (k : ℝ) ^ 2) - ∑ i ∈ Finset.range m, 1 / (i : ℝ) ^ 2 := by
      have := hsplit
      -- ∑range + tail = total
      push_cast at this ⊢
      linarith [this]
    rw [this]; linarith
  linarith [tsum_inv_sq_le]

/-- Main tail bound. -/
theorem tail_pow_le (m q : ℕ) (hm : 1 ≤ m) :
    (∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ (q + 2)) ≤ (1 / (m : ℝ) ^ (q + 2)) * (m : ℝ) ^ 2 * 2 := by
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- termwise bound
  have hterm : ∀ k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ (q + 2)
      ≤ ((1 / (m : ℝ) ^ (q + 2)) * (m : ℝ) ^ 2) * (1 / ((k + m : ℕ) : ℝ) ^ 2) := by
    intro k
    set X : ℝ := ((k + m : ℕ) : ℝ) with hXdef
    have hkm : (0 : ℝ) < X := by rw [hXdef]; exact_mod_cast (by omega : 0 < k + m)
    have hle : (m : ℝ) ≤ X := by rw [hXdef]; exact_mod_cast (by omega : m ≤ k + m)
    have hpow : (m : ℝ) ^ q ≤ X ^ q := pow_le_pow_left₀ hmr.le hle q
    have key : (1 : ℝ) * ((m : ℝ) ^ (q + 2) * X ^ 2) ≤ (m : ℝ) ^ 2 * X ^ (q + 2) := by
      have e1 : (m : ℝ) ^ (q + 2) = (m : ℝ) ^ q * (m : ℝ) ^ 2 := by rw [pow_add]
      have e2 : X ^ (q + 2) = X ^ q * X ^ 2 := by rw [pow_add]
      rw [e1, e2, one_mul]
      have : (m : ℝ) ^ q * ((m : ℝ) ^ 2 * X ^ 2) ≤ X ^ q * ((m : ℝ) ^ 2 * X ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      nlinarith [this]
    have hRHS : ((1 / (m : ℝ) ^ (q + 2)) * (m : ℝ) ^ 2) * (1 / X ^ 2)
        = (m : ℝ) ^ 2 / ((m : ℝ) ^ (q + 2) * X ^ 2) := by
      field_simp
    rw [hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
    exact key
  calc (∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ (q + 2))
      ≤ ∑' k : ℕ, ((1 / (m : ℝ) ^ (q + 2)) * (m : ℝ) ^ 2) * (1 / ((k + m : ℕ) : ℝ) ^ 2) := by
        exact Summable.tsum_mono (summable_shift (q + 2) m (by omega))
          ((summable_shift 2 m (le_refl 2)).mul_left _) hterm
    _ = ((1 / (m : ℝ) ^ (q + 2)) * (m : ℝ) ^ 2) * ∑' k : ℕ, (1 / ((k + m : ℕ) : ℝ) ^ 2) :=
        (Summable.tsum_mul_left _ (summable_shift 2 m (le_refl 2)))
    _ ≤ ((1 / (m : ℝ) ^ (q + 2)) * (m : ℝ) ^ 2) * 2 := by
        apply mul_le_mul_of_nonneg_left (tail2_le m)
        positivity

set_option maxHeartbeats 1000000 in
/-- Core bound with `g, h0` as opaque parameters (fast for `nlinarith`). -/
theorem poly_bound_core (y2 y3 y5 y7 g h0 L : ℝ)
    (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3) (hy5 : 0 ≤ y5) (hy7 : 0 ≤ y7)
    (o75 : y7 ≤ y5) (o53 : y5 ≤ y3) (o32 : y3 ≤ y2)
    (hg0 : 0 ≤ g) (hg4 : g ≤ 4 * y2) (hg1 : g ≤ 1)
    (hh00 : 0 ≤ h0) (hh05 : h0 ≤ 5 * y2 ^ 2)
    (hL : 0 ≤ L)
    (b_27 : y2 * y7 ≤ L) (b_35 : y3 * y5 ≤ L) (b_37 : y3 * y7 ≤ L)
    (b_55 : y5 * y5 ≤ L) (b_57 : y5 * y7 ≤ L) (b_77 : y7 * y7 ≤ L)
    (b_223 : y2 * y2 * y3 ≤ L) (b_233 : y2 * y3 * y3 ≤ L)
    (b_2222 : y2 * y2 * y2 * y2 ≤ L) :
    |(- (2 * y2 * y7 + 2 * y3 * y5 + 2 * y3 * y7 + (y5 + y7) ^ 2
          + (y3 + y5 + y7) * (g ^ 2 + g * y2 + 2 * y2 ^ 2) + g * y3 ^ 2))
        - 2 * g ^ 2 * h0 + (1 - g) * h0 ^ 2| ≤ 240 * L := by
  have t4 : (y5 + y7) ^ 2 ≤ 4 * L := by nlinarith [b_55, b_57, b_77]
  have t5 : (y3 + y5 + y7) * (g ^ 2 + g * y2 + 2 * y2 ^ 2) ≤ 66 * L := by
    have hA : y3 + y5 + y7 ≤ 3 * y3 := by linarith
    have hB : g ^ 2 + g * y2 + 2 * y2 ^ 2 ≤ 22 * y2 ^ 2 := by nlinarith [hg4, hg0, hy2]
    have hBpos : 0 ≤ g ^ 2 + g * y2 + 2 * y2 ^ 2 := by nlinarith [sq_nonneg g, mul_nonneg hg0 hy2, sq_nonneg y2]
    calc (y3 + y5 + y7) * (g ^ 2 + g * y2 + 2 * y2 ^ 2)
        ≤ (3 * y3) * (22 * y2 ^ 2) := by
          apply mul_le_mul hA hB hBpos (by linarith)
      _ = 66 * (y2 * y2 * y3) := by ring
      _ ≤ 66 * L := by nlinarith [b_223]
  have t6 : g * y3 ^ 2 ≤ 4 * L := by
    have : g * y3 ^ 2 ≤ (4 * y2) * y3 ^ 2 :=
      mul_le_mul_of_nonneg_right hg4 (by positivity)
    nlinarith [this, b_233]
  have hWnonneg : 0 ≤ 2 * y2 * y7 + 2 * y3 * y5 + 2 * y3 * y7 + (y5 + y7) ^ 2
      + (y3 + y5 + y7) * (g ^ 2 + g * y2 + 2 * y2 ^ 2) + g * y3 ^ 2 := by
    have p1 : 0 ≤ (y3 + y5 + y7) * (g ^ 2 + g * y2 + 2 * y2 ^ 2) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg g, mul_nonneg hg0 hy2, sq_nonneg y2])
    have p2 : 0 ≤ g * y3 ^ 2 := mul_nonneg hg0 (by positivity)
    nlinarith [mul_nonneg hy2 hy7, mul_nonneg hy3 hy5, mul_nonneg hy3 hy7, sq_nonneg (y5 + y7), p1, p2]
  have hW80 : 2 * y2 * y7 + 2 * y3 * y5 + 2 * y3 * y7 + (y5 + y7) ^ 2
      + (y3 + y5 + y7) * (g ^ 2 + g * y2 + 2 * y2 ^ 2) + g * y3 ^ 2 ≤ 80 * L := by
    nlinarith [t4, t5, t6, b_27, b_35, b_37]
  have hgh : 2 * g ^ 2 * h0 ≤ 160 * L := by
    have hg2 : g ^ 2 ≤ 16 * y2 ^ 2 := by
      nlinarith [mul_le_mul hg4 hg4 hg0 (by linarith : (0:ℝ) ≤ 4 * y2)]
    have h1 : g ^ 2 * h0 ≤ (16 * y2 ^ 2) * (5 * y2 ^ 2) :=
      mul_le_mul hg2 hh05 hh00 (by positivity)
    calc 2 * g ^ 2 * h0 = 2 * (g ^ 2 * h0) := by ring
      _ ≤ 2 * ((16 * y2 ^ 2) * (5 * y2 ^ 2)) := by
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 160 * (y2 * y2 * y2 * y2) := by ring
      _ ≤ 160 * L := by linarith [b_2222]
  have hgh2u : (1 - g) * h0 ^ 2 ≤ 25 * L := by
    have hh02 : h0 ^ 2 ≤ (5 * y2 ^ 2) * (5 * y2 ^ 2) := by
      have := mul_le_mul hh05 hh05 hh00 (by positivity : (0:ℝ) ≤ 5 * y2 ^ 2)
      nlinarith [this]
    calc (1 - g) * h0 ^ 2 ≤ 1 * ((5 * y2 ^ 2) * (5 * y2 ^ 2)) :=
          mul_le_mul (by linarith) hh02 (by positivity) (by linarith)
      _ = 25 * (y2 * y2 * y2 * y2) := by ring
      _ ≤ 25 * L := by linarith [b_2222]
  have hgh2l : 0 ≤ (1 - g) * h0 ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hgh0 : 0 ≤ 2 * g ^ 2 * h0 := by
    have : 2 * g ^ 2 * h0 = (2 * g ^ 2) * h0 := by ring
    rw [this]; exact mul_nonneg (by positivity) hh00
  rw [abs_le]
  constructor
  · linarith [hW80, hgh, hgh2l]
  · linarith [hWnonneg, hgh0, hgh2u]

/-- Generic: `1/c^n ≤ 1/11^n` when `11 ≤ c`. -/
theorem inv_pow_le_11 (n : ℕ) (c : ℝ) (hc : (11:ℝ) ≤ c) : 1 / c ^ n ≤ 1 / (11:ℝ) ^ n := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by norm_num) hc n

/-- Generic ordering: `1/a^n ≤ 1/b^n` when `0 < b ≤ a`. -/
theorem inv_pow_mono (n : ℕ) (a b : ℝ) (hb : 0 < b) (hab : b ≤ a) :
    1 / a ^ n ≤ 1 / b ^ n :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hb.le hab n)

/-- The core finite polynomial bound (`M_fin`), abstractly in atoms `y2,y3,y5,y7`. -/
theorem key_poly_bound (y2 y3 y5 y7 L : ℝ)
    (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3) (hy5 : 0 ≤ y5) (hy7 : 0 ≤ y7)
    (o75 : y7 ≤ y5) (o53 : y5 ≤ y3) (o32 : y3 ≤ y2) (hy2q : y2 ≤ 1/4)
    (hL : 0 ≤ L)
    (b_27 : y2 * y7 ≤ L) (b_35 : y3 * y5 ≤ L) (b_37 : y3 * y7 ≤ L)
    (b_55 : y5 * y5 ≤ L) (b_57 : y5 * y7 ≤ L) (b_77 : y7 * y7 ≤ L)
    (b_223 : y2 * y2 * y3 ≤ L) (b_233 : y2 * y3 * y3 ≤ L)
    (b_2222 : y2 * y2 * y2 * y2 ≤ L) :
    |(1 - (y2 + y3 + y5 + y7)) *
        (1 + ((y2 + y3 + y5 + y7) + (y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5))) ^ 2
      - (1 + (y2 + y3 + y5 + y7)) * (1 + (y2 ^ 2 + y3 ^ 2))| ≤ 240 * L := by
  have hg0 : 0 ≤ y2 + y3 + y5 + y7 := by linarith
  have hg4 : y2 + y3 + y5 + y7 ≤ 4 * y2 := by linarith
  have hg1 : y2 + y3 + y5 + y7 ≤ 1 := by linarith
  have hh00 : 0 ≤ y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5 := by positivity
  have hh05 : y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5 ≤ 5 * y2 ^ 2 := by
    have e1 : y2 * y3 ≤ y2 ^ 2 := by nlinarith
    have e2 : y2 ^ 3 ≤ y2 ^ 2 := by nlinarith
    have e3 : y3 ^ 2 ≤ y2 ^ 2 := by nlinarith
    have e4 : y2 * y5 ≤ y2 ^ 2 := by nlinarith
    linarith
  have hid : (1 - (y2 + y3 + y5 + y7)) *
        (1 + ((y2 + y3 + y5 + y7) + (y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5))) ^ 2
      - (1 + (y2 + y3 + y5 + y7)) * (1 + (y2 ^ 2 + y3 ^ 2))
      = (- (2 * y2 * y7 + 2 * y3 * y5 + 2 * y3 * y7 + (y5 + y7) ^ 2
          + (y3 + y5 + y7) * ((y2 + y3 + y5 + y7) ^ 2 + (y2 + y3 + y5 + y7) * y2 + 2 * y2 ^ 2)
          + (y2 + y3 + y5 + y7) * y3 ^ 2))
        - 2 * (y2 + y3 + y5 + y7) ^ 2 * (y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5)
        + (1 - (y2 + y3 + y5 + y7)) * (y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5) ^ 2 := by
    ring
  rw [hid]
  exact poly_bound_core y2 y3 y5 y7 (y2 + y3 + y5 + y7)
    (y2 ^ 2 + y2 * y3 + y2 ^ 3 + y3 ^ 2 + y2 * y5) L
    hy2 hy3 hy5 hy7 o75 o53 o32 hg0 hg4 hg1 hh00 hh05 hL
    b_27 b_35 b_37 b_55 b_57 b_77 b_223 b_233 b_2222


/-- Bound on the tail-error term `E`. -/
theorem E_bound (gg P T U L : ℝ)
    (hg0 : 0 ≤ gg) (hg1 : gg ≤ 1) (hP1 : 1 ≤ P) (hP2 : P ≤ 2)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hTb : T ≤ 242 * L)
    (hU0 : 0 ≤ U) (hUb : U ≤ 32 * L) (hL : 0 ≤ L) :
    |(1 - gg) * (2 * P * T + T ^ 2) - (1 + gg) * U| ≤ 1210 * L := by
  have hX0 : 0 ≤ 2 * P * T + T ^ 2 := by nlinarith [hP1, hT0, sq_nonneg T]
  have hX5 : 2 * P * T + T ^ 2 ≤ 5 * T := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 - P by linarith) hT0,
      mul_nonneg (show (0:ℝ) ≤ 1 - T by linarith) hT0]
  have hUU : 0 ≤ (1 + gg) * U := mul_nonneg (by linarith) hU0
  have hUU2 : (1 + gg) * U ≤ 2 * U := by nlinarith [hU0]
  have hnn : 0 ≤ (1 - gg) * (2 * P * T + T ^ 2) := mul_nonneg (by linarith) hX0
  have hup : (1 - gg) * (2 * P * T + T ^ 2) ≤ 5 * T := by
    nlinarith [mul_nonneg hg0 hX0, hX5]
  rw [abs_le]
  constructor
  · nlinarith [hnn, hUU2, hUb, hTb, hL]
  · nlinarith [hup, hUU, hTb, hL]

/-- Abstract splitting identity (cheap `ring`, avoids expanding the huge zeta sums). -/
theorem M_split (g P Q T U : ℝ) :
    (1 - g) * (P + T) ^ 2 - (1 + g) * (Q + U)
      = ((1 - g) * P ^ 2 - (1 + g) * Q)
        + ((1 - g) * (2 * P * T + T ^ 2) - (1 + g) * U) := by ring

set_option maxHeartbeats 4000000 in
theorem main_bound (n : ℕ) (hn : 4 ≤ n) :
    |(1 - A114362_t n) / (1 + A114362_t n)
      - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)|
      ≤ 725 / (11:ℝ) ^ n := by
  have hn1 : 1 < n := by omega
  -- zeta as real sums
  have hZ1v : (riemannZeta (n:ℂ)).re = ∑' k : ℕ, 1 / (k:ℝ) ^ n := zeta_re_eq n hn1
  have hZ2v : (riemannZeta (2 * (n:ℂ))).re = ∑' k : ℕ, 1 / (k:ℝ) ^ (2 * n) :=
    zeta_re_eq2 n (by omega)
  have htdef : A114362_t n = (riemannZeta (2 * (n:ℂ))).re / ((riemannZeta (n:ℂ)).re) ^ 2 := rfl
  set Z1 := (riemannZeta (n:ℂ)).re with hZ1def
  set Z2 := (riemannZeta (2 * (n:ℂ))).re with hZ2def
  -- atoms
  -- Peel Z1
  have hsum1 : Summable (fun k : ℕ => 1 / (k:ℝ) ^ n) := Real.summable_one_div_nat_pow.mpr hn1
  have hsplit1 := hsum1.sum_add_tsum_nat_add 11
  have hfin1 : ∑ i ∈ Finset.range 11, 1 / ((i:ℕ):ℝ) ^ n
      = 1 + (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (4:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (6:ℝ) ^ n
        + 1 / (7:ℝ) ^ n + 1 / (8:ℝ) ^ n + 1 / (9:ℝ) ^ n + 1 / (10:ℝ) ^ n) := by
    have h0 : (0:ℝ) ^ n = 0 := zero_pow (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast; rw [h0]; norm_num; ring
  -- conversions literal -> atom
  have c4 : 1 / (4:ℝ) ^ n = (1 / (2:ℝ) ^ n) ^ 2 := by
    rw [div_pow, one_pow, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have c6 : 1 / (6:ℝ) ^ n = (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) := by
    rw [div_mul_div_comm, one_mul, ← mul_pow]; norm_num
  have c8 : 1 / (8:ℝ) ^ n = (1 / (2:ℝ) ^ n) ^ 3 := by
    rw [div_pow, one_pow, show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have c9 : 1 / (9:ℝ) ^ n = (1 / (3:ℝ) ^ n) ^ 2 := by
    rw [div_pow, one_pow, show (9:ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have c10 : 1 / (10:ℝ) ^ n = (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n) := by
    rw [div_mul_div_comm, one_mul, ← mul_pow]; norm_num
  -- T tail
  set T := ∑' i : ℕ, 1 / ((i + 11 : ℕ):ℝ) ^ n with hTdef
  have hZ1eq : Z1 = (1 + ((1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
      + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
         + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n)))) + T := by
    have : Z1 = ∑ i ∈ Finset.range 11, 1 / ((i:ℕ):ℝ) ^ n + T := by
      rw [hZ1v, hTdef, ← hsplit1]
    rw [this, hfin1, c4, c6, c8, c9, c10]; ring
  -- Peel Z2
  have hsum2 : Summable (fun k : ℕ => 1 / (k:ℝ) ^ (2 * n)) := Real.summable_one_div_nat_pow.mpr (by omega)
  have hsplit2 := hsum2.sum_add_tsum_nat_add 4
  have hfin2 : ∑ i ∈ Finset.range 4, 1 / ((i:ℕ):ℝ) ^ (2 * n)
      = 1 + (1 / (2:ℝ) ^ (2 * n) + 1 / (3:ℝ) ^ (2 * n)) := by
    have h0 : (0:ℝ) ^ (2 * n) = 0 := zero_pow (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast; rw [h0]; norm_num; ring
  have d2 : 1 / (2:ℝ) ^ (2 * n) = (1 / (2:ℝ) ^ n) ^ 2 := by
    rw [div_pow, one_pow, ← pow_mul, mul_comm]
  have d3 : 1 / (3:ℝ) ^ (2 * n) = (1 / (3:ℝ) ^ n) ^ 2 := by
    rw [div_pow, one_pow, ← pow_mul, mul_comm]
  set U := ∑' i : ℕ, 1 / ((i + 4 : ℕ):ℝ) ^ (2 * n) with hUdef
  have hZ2eq : Z2 = (1 + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (3:ℝ) ^ n) ^ 2)) + U := by
    have : Z2 = ∑ i ∈ Finset.range 4, 1 / ((i:ℕ):ℝ) ^ (2 * n) + U := by
      rw [hZ2v, hUdef, ← hsplit2]
    rw [this, hfin2, d2, d3]
  clear_value Z1 Z2
  -- === bounds ===
  have hy2nn : (0:ℝ) ≤ 1 / (2:ℝ) ^ n := by positivity
  have hy3nn : (0:ℝ) ≤ 1 / (3:ℝ) ^ n := by positivity
  have hy5nn : (0:ℝ) ≤ 1 / (5:ℝ) ^ n := by positivity
  have hy7nn : (0:ℝ) ≤ 1 / (7:ℝ) ^ n := by positivity
  have o32 : 1 / (3:ℝ) ^ n ≤ 1 / (2:ℝ) ^ n := inv_pow_mono n 3 2 (by norm_num) (by norm_num)
  have o53 : 1 / (5:ℝ) ^ n ≤ 1 / (3:ℝ) ^ n := inv_pow_mono n 5 3 (by norm_num) (by norm_num)
  have o75 : 1 / (7:ℝ) ^ n ≤ 1 / (5:ℝ) ^ n := inv_pow_mono n 7 5 (by norm_num) (by norm_num)
  have h16 : (16:ℝ) ≤ (2:ℝ) ^ n := by
    calc (16:ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hy2_16 : 1 / (2:ℝ) ^ n ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) h16
  have hy2q : 1 / (2:ℝ) ^ n ≤ 1 / 4 := by linarith
  have hy2_1 : 1 / (2:ℝ) ^ n ≤ 1 := by linarith
  have hy3_1 : 1 / (3:ℝ) ^ n ≤ 1 := le_trans o32 hy2_1
  have hy5_1 : 1 / (5:ℝ) ^ n ≤ 1 := le_trans o53 hy3_1
  have hL0 : (0:ℝ) ≤ 1 / (11:ℝ) ^ n := by positivity
  -- product bounds
  have b_27 : (1 / (2:ℝ) ^ n) * (1 / (7:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (2:ℝ) ^ n) * (1 / (7:ℝ) ^ n) = 1 / (14:ℝ) ^ n by
      rw [show (14:ℝ) = 2 * 7 by norm_num, mul_pow]; ring]
    exact inv_pow_le_11 n 14 (by norm_num)
  have b_35 : (1 / (3:ℝ) ^ n) * (1 / (5:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (3:ℝ) ^ n) * (1 / (5:ℝ) ^ n) = 1 / (15:ℝ) ^ n by
      rw [show (15:ℝ) = 3 * 5 by norm_num, mul_pow]; ring]
    exact inv_pow_le_11 n 15 (by norm_num)
  have b_37 : (1 / (3:ℝ) ^ n) * (1 / (7:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (3:ℝ) ^ n) * (1 / (7:ℝ) ^ n) = 1 / (21:ℝ) ^ n by
      rw [show (21:ℝ) = 3 * 7 by norm_num, mul_pow]; ring]
    exact inv_pow_le_11 n 21 (by norm_num)
  have b_55 : (1 / (5:ℝ) ^ n) * (1 / (5:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (5:ℝ) ^ n) * (1 / (5:ℝ) ^ n) = 1 / (25:ℝ) ^ n by
      rw [show (25:ℝ) = 5 * 5 by norm_num, mul_pow]; ring]
    exact inv_pow_le_11 n 25 (by norm_num)
  have b_57 : (1 / (5:ℝ) ^ n) * (1 / (7:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (5:ℝ) ^ n) * (1 / (7:ℝ) ^ n) = 1 / (35:ℝ) ^ n by
      rw [show (35:ℝ) = 5 * 7 by norm_num, mul_pow]; ring]
    exact inv_pow_le_11 n 35 (by norm_num)
  have b_77 : (1 / (7:ℝ) ^ n) * (1 / (7:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (7:ℝ) ^ n) * (1 / (7:ℝ) ^ n) = 1 / (49:ℝ) ^ n by
      rw [show (49:ℝ) = 7 * 7 by norm_num, mul_pow]; ring]
    exact inv_pow_le_11 n 49 (by norm_num)
  have b_223 : (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) = 1 / (12:ℝ) ^ n by
      rw [show (12:ℝ) = 2 * 2 * 3 by norm_num, mul_pow, mul_pow]; ring]
    exact inv_pow_le_11 n 12 (by norm_num)
  have b_233 : (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) * (1 / (3:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) * (1 / (3:ℝ) ^ n) = 1 / (18:ℝ) ^ n by
      rw [show (18:ℝ) = 2 * 3 * 3 by norm_num, mul_pow, mul_pow]; ring]
    exact inv_pow_le_11 n 18 (by norm_num)
  have b_2222 : (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) ≤ 1 / (11:ℝ) ^ n := by
    rw [show (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) = 1 / (16:ℝ) ^ n by
      rw [show (16:ℝ) = 2 * 2 * 2 * 2 by norm_num, mul_pow, mul_pow, mul_pow]; ring]
    exact inv_pow_le_11 n 16 (by norm_num)
  -- M_fin bound
  have hMfin := key_poly_bound (1 / (2:ℝ) ^ n) (1 / (3:ℝ) ^ n) (1 / (5:ℝ) ^ n) (1 / (7:ℝ) ^ n)
    (1 / (11:ℝ) ^ n) hy2nn hy3nn hy5nn hy7nn o75 o53 o32 hy2q hL0
    b_27 b_35 b_37 b_55 b_57 b_77 b_223 b_233 b_2222
  -- T, U bounds
  have hT0 : 0 ≤ T := by rw [hTdef]; exact tsum_nonneg (fun i => by positivity)
  have hTb : T ≤ 242 * (1 / (11:ℝ) ^ n) := by
    have key := tail_pow_le 11 (n - 2) (by norm_num)
    rw [show n - 2 + 2 = n by omega] at key
    calc T = ∑' i : ℕ, 1 / ((i + 11 : ℕ):ℝ) ^ n := hTdef
      _ ≤ (1 / (11:ℝ) ^ n) * (11:ℝ) ^ 2 * 2 := key
      _ = 242 * (1 / (11:ℝ) ^ n) := by rw [show (11:ℝ) ^ 2 = 121 by norm_num]; ring
  have hU0 : 0 ≤ U := by rw [hUdef]; exact tsum_nonneg (fun i => by positivity)
  have hUb : U ≤ 32 * (1 / (11:ℝ) ^ n) := by
    have key := tail_pow_le 4 (2 * n - 2) (by norm_num)
    rw [show 2 * n - 2 + 2 = 2 * n by omega] at key
    have e16 : 1 / (4:ℝ) ^ (2 * n) = 1 / (16:ℝ) ^ n := by
      rw [show (16:ℝ) = 4 ^ 2 by norm_num, ← pow_mul, mul_comm]
    calc U = ∑' i : ℕ, 1 / ((i + 4 : ℕ):ℝ) ^ (2 * n) := hUdef
      _ ≤ (1 / (4:ℝ) ^ (2 * n)) * (4:ℝ) ^ 2 * 2 := key
      _ = 32 * (1 / (16:ℝ) ^ n) := by rw [e16, show (4:ℝ) ^ 2 = 16 by norm_num]; ring
      _ ≤ 32 * (1 / (11:ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left (inv_pow_le_11 n 16 (by norm_num)) (by norm_num)
  -- Z1, Z2 lower bounds
  have hghnn : (0:ℝ) ≤ (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
      + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
         + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n)) := by positivity
  have hZ1ge : 1 ≤ Z1 := by rw [hZ1eq]; linarith [hghnn, hT0]
  have hZ1pos : 0 < Z1 := by linarith
  have hZ1ne : Z1 ≠ 0 := ne_of_gt hZ1pos
  have hfbnn : (0:ℝ) ≤ (1 / (2:ℝ) ^ n) ^ 2 + (1 / (3:ℝ) ^ n) ^ 2 := by positivity
  have hZ2ge : 1 ≤ Z2 := by rw [hZ2eq]; linarith [hfbnn, hU0]
  have hZ2pos : 0 < Z2 := by linarith
  have hZ1sq : 1 ≤ Z1 ^ 2 := one_le_pow₀ hZ1ge
  have hDpos : 0 < Z1 ^ 2 + Z2 := by positivity
  have hD2 : 2 ≤ Z1 ^ 2 + Z2 := by linarith
  -- g, P bounds for E
  have hg0' : (0:ℝ) ≤ 1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n := by positivity
  have hg1' : 1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n ≤ 1 := by linarith
  have hsq2 : (1 / (2:ℝ) ^ n) ^ 2 ≤ 1 / (2:ℝ) ^ n := by
    rw [sq]
    calc (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) ≤ (1 / (2:ℝ) ^ n) * 1 :=
          mul_le_mul_of_nonneg_left hy2_1 hy2nn
      _ = 1 / (2:ℝ) ^ n := mul_one _
  have hm23 : (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) ≤ 1 / (2:ℝ) ^ n := by
    calc (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) ≤ (1 / (2:ℝ) ^ n) * 1 :=
          mul_le_mul_of_nonneg_left hy3_1 hy2nn
      _ = 1 / (2:ℝ) ^ n := mul_one _
  have hcube2 : (1 / (2:ℝ) ^ n) ^ 3 ≤ 1 / (2:ℝ) ^ n := by
    calc (1 / (2:ℝ) ^ n) ^ 3 = (1 / (2:ℝ) ^ n) * ((1 / (2:ℝ) ^ n) ^ 2) := by ring
      _ ≤ (1 / (2:ℝ) ^ n) * (1 / (2:ℝ) ^ n) := mul_le_mul_of_nonneg_left hsq2 hy2nn
      _ ≤ (1 / (2:ℝ) ^ n) * 1 := mul_le_mul_of_nonneg_left hy2_1 hy2nn
      _ = 1 / (2:ℝ) ^ n := mul_one _
  have hsq3 : (1 / (3:ℝ) ^ n) ^ 2 ≤ 1 / (2:ℝ) ^ n := by
    rw [sq]
    calc (1 / (3:ℝ) ^ n) * (1 / (3:ℝ) ^ n) ≤ (1 / (3:ℝ) ^ n) * 1 :=
          mul_le_mul_of_nonneg_left hy3_1 hy3nn
      _ = 1 / (3:ℝ) ^ n := mul_one _
      _ ≤ 1 / (2:ℝ) ^ n := o32
  have hm25 : (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n) ≤ 1 / (2:ℝ) ^ n := by
    calc (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n) ≤ (1 / (2:ℝ) ^ n) * 1 :=
          mul_le_mul_of_nonneg_left hy5_1 hy2nn
      _ = 1 / (2:ℝ) ^ n := mul_one _
  have hP1 : (1:ℝ) ≤ 1 + ((1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
      + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
         + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n))) := by linarith [hghnn]
  have hP2 : (1 + ((1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
      + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
         + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n)))) ≤ 2 := by
    -- g+h0 ≤ 9*y2 ≤ 9/16 ≤ 1
    have : (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
        + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
           + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n))
        ≤ 9 * (1 / (2:ℝ) ^ n) := by linarith [o32, o53, o75, hsq2, hm23, hcube2, hsq3, hm25]
    linarith [this, hy2_16]
  -- T ≤ 1
  have h11n : (242:ℝ) ≤ (11:ℝ) ^ n := by
    calc (242:ℝ) ≤ 11 ^ 4 := by norm_num
      _ ≤ 11 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h242 : 242 * (1 / (11:ℝ) ^ n) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]; exact h11n
  have hT1 : T ≤ 1 := le_trans hTb h242
  -- E bound
  have hEabs := E_bound (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
    (1 + ((1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
      + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
         + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n)))) T U (1 / (11:ℝ) ^ n)
    hg0' hg1' hP1 hP2 hT0 hT1 hTb hU0 hUb hL0
  -- combine M = M_fin + E
  have hMid : (1 - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * Z1 ^ 2
        - (1 + (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * Z2
      = ((1 - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) *
          (1 + ((1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
             + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
                + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n)))) ^ 2
          - (1 + (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) *
            (1 + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (3:ℝ) ^ n) ^ 2)))
        + ((1 - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) *
            (2 * (1 + ((1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
              + ((1 / (2:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (3:ℝ) ^ n) + (1 / (2:ℝ) ^ n) ^ 3
                 + (1 / (3:ℝ) ^ n) ^ 2 + (1 / (2:ℝ) ^ n) * (1 / (5:ℝ) ^ n)))) * T + T ^ 2)
          - (1 + (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * U) := by
    rw [hZ1eq, hZ2eq]; exact M_split _ _ _ _ _
  have hMabs : |(1 - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * Z1 ^ 2
        - (1 + (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * Z2|
      ≤ 1450 * (1 / (11:ℝ) ^ n) := by
    rw [hMid]
    calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ 240 * (1 / (11:ℝ) ^ n) + 1210 * (1 / (11:ℝ) ^ n) := by linarith [hMfin, hEabs]
      _ = 1450 * (1 / (11:ℝ) ^ n) := by ring
  -- final assembly
  rw [htdef]
  have hfrac : (1 - Z2 / Z1 ^ 2) / (1 + Z2 / Z1 ^ 2)
      - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)
      = ((1 - (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * Z1 ^ 2
          - (1 + (1 / (2:ℝ) ^ n + 1 / (3:ℝ) ^ n + 1 / (5:ℝ) ^ n + 1 / (7:ℝ) ^ n)) * Z2)
        / (Z1 ^ 2 + Z2) := by
    have h1' : Z1 ^ 2 ≠ 0 := pow_ne_zero _ hZ1ne
    have hD : Z1 ^ 2 + Z2 ≠ 0 := ne_of_gt hDpos
    have hne : 1 + Z2 / Z1 ^ 2 ≠ 0 := by
      have : 1 + Z2 / Z1 ^ 2 = (Z1 ^ 2 + Z2) / Z1 ^ 2 := by field_simp
      rw [this]; positivity
    field_simp
    ring
  rw [hfrac, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have hmul : 725 / (11:ℝ) ^ n * 2 ≤ 725 / (11:ℝ) ^ n * (Z1 ^ 2 + Z2) :=
    mul_le_mul_of_nonneg_left hD2 (by positivity)
  have he : 725 / (11:ℝ) ^ n * 2 = 1450 * (1 / (11:ℝ) ^ n) := by ring
  linarith [hMabs, hmul, he]

theorem oeis_A114362_conjecture_1 :
    (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨725, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨4, fun n hn => ?_⟩
  have h := main_bound n hn
  have hpos : (0:ℝ) < 1 / (11:ℝ) ^ n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
  calc |(1 - A114362_t n) / (1 + A114362_t n) -
        (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n)|
      ≤ 725 / (11:ℝ) ^ n := h
    _ = 725 * (1 / (11:ℝ) ^ n) := by ring
