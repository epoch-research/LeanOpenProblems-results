import FormalConjectures.Util.ProblemImports


open scoped Nat Topology

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


lemma inv_pow_base_bigO (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (fun n : ℕ => 1 / a ^ n) =O[atTop] (fun n : ℕ => 1 / b ^ n) := by
  refine (isBigO_iff.2 ?_)
  refine ⟨1, Eventually.of_forall ?_⟩
  intro n
  have hpow : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb.le hba n
  have hbp : 0 < b ^ n := pow_pos hb n
  have hap : 0 < a ^ n := pow_pos ha n
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hap), abs_of_pos (one_div_pos.mpr hbp), one_mul]
  exact one_div_le_one_div_of_le hbp hpow

lemma tail_summable (m n : ℕ) (hm : 0 < m) (hn : 1 < n) :
    Summable (fun k : ℕ => 1 / ((k + m : ℕ) : ℝ) ^ n) := by
  have hs : Summable (fun k : ℕ => 1 / |(k : ℝ) + (m : ℝ)| ^ (n : ℝ)) := by
    exact (Real.summable_one_div_nat_add_rpow (m : ℝ) (n : ℝ)).mpr (by exact_mod_cast hn)
  convert hs using 2 with k
  have hpos : 0 ≤ (k : ℝ) + (m : ℝ) := by positivity
  rw [abs_of_nonneg hpos]
  norm_cast

noncomputable def tailConst (m : ℕ) : ℝ :=
  (m : ℝ)^2 * (∑' k : ℕ, 1 / ((k+1 : ℕ) : ℝ)^2)

lemma tail_bound (m n : ℕ) (hm : 0 < m) (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ n) ≤ tailConst m * (1 / (m : ℝ)^n) := by
  let f : ℕ → ℝ := fun k => 1 / ((k + m : ℕ) : ℝ) ^ n
  let g : ℕ → ℝ := fun k => ((m : ℝ)^2 * (1 / (m : ℝ)^n)) * (1 / ((k+1 : ℕ) : ℝ)^2)
  have hfg : ∀ k, f k ≤ g k := by
    intro k
    dsimp [f, g]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hk1 : 0 < ((k+1 : ℕ) : ℝ) := by positivity
    have h1 : (m : ℝ) ^ (n - 2) * ((k+1 : ℕ) : ℝ)^2 ≤ ((k + m : ℕ) : ℝ) ^ n := by
      have hm_le : (m : ℝ) ≤ ((k + m : ℕ) : ℝ) := by norm_cast; omega
      have hk_le : ((k+1 : ℕ) : ℝ) ≤ ((k + m : ℕ) : ℝ) := by norm_cast; omega
      have hpow1 := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ)) hm_le (n - 2)
      have hpow2 := pow_le_pow_left₀ (by positivity : 0 ≤ ((k+1 : ℕ) : ℝ)) hk_le 2
      have hmul := mul_le_mul hpow1 hpow2 (pow_nonneg (by positivity) 2) (pow_nonneg (by positivity) (n-2))
      calc
        (m : ℝ) ^ (n - 2) * ((k+1 : ℕ) : ℝ)^2 ≤ ((k + m : ℕ) : ℝ) ^ (n-2) * ((k + m : ℕ) : ℝ)^2 := hmul
        _ = ((k + m : ℕ) : ℝ) ^ n := by
          rw [← pow_add]
          have : n - 2 + 2 = n := by omega
          rw [this]
    have hdenpos : 0 < (m : ℝ) ^ (n - 2) * ((k+1 : ℕ) : ℝ)^2 := by positivity
    have hmain := one_div_le_one_div_of_le hdenpos h1
    calc
      1 / ((k + m : ℕ) : ℝ) ^ n ≤ 1 / ((m : ℝ) ^ (n-2) * ((k+1 : ℕ) : ℝ)^2) := hmain
      _ = (m : ℝ)^2 * (1 / (m : ℝ)^n) * (1 / ((k+1 : ℕ) : ℝ)^2) := by
        field_simp [pow_ne_zero _ hmR.ne', hk1.ne']
        rw [← pow_add]
        have : n - 2 + 2 = n := by omega
        rw [this]
  have hg_sum : Summable g := by
    dsimp [g]
    exact (tail_summable 1 2 (by norm_num) (by norm_num)).mul_left _
  have hf_sum : Summable f := tail_summable m n hm (by omega)
  calc
    (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k := hf_sum.tsum_le_tsum hfg hg_sum
    _ = tailConst m * (1 / (m : ℝ)^n) := by
      dsimp [g, tailConst]
      rw [(tail_summable 1 2 (by norm_num) (by norm_num)).tsum_mul_left]
      ring

lemma tail_tsum_bigO (m : ℕ) (hm : 0 < m) (hm11 : 11 ≤ m) :
    (fun n : ℕ => ∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ n) =O[atTop]
      (fun n : ℕ => 1 / (11:ℝ)^n) := by
  refine isBigO_iff.2 ⟨tailConst m, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnon : 0 ≤ ∑' k : ℕ, 1 / ((k + m : ℕ) : ℝ) ^ n := by
    apply tsum_nonneg
    intro k
    positivity
  have hle := tail_bound m n hm hn
  have hmR : (11:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm11
  have hmposR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hbase := inv_pow_base_bigO (m:ℝ) (11:ℝ) hmposR (by norm_num) hmR
  have hpow : 1 / (m : ℝ)^n ≤ 1 / (11:ℝ)^n := by
    have hpow' : (11:ℝ)^n ≤ (m:ℝ)^n := pow_le_pow_left₀ (by norm_num) hmR n
    exact one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ) < 11) n) hpow'
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hnon, abs_of_pos (one_div_pos.mpr (pow_pos (by norm_num : (0:ℝ) < 11) n))]
  exact hle.trans (mul_le_mul_of_nonneg_left hpow (by unfold tailConst; positivity))


lemma zeta_term_conv (k n : ℕ) :
    1 / ((k : ℂ) + 1) ^ (n : ℂ) = (1 / (((k+1 : ℕ) : ℝ) ^ n) : ℂ) := by
  rw [Complex.cpow_natCast]
  norm_num

lemma zeta_re_eq_tsum (n : ℕ) (hn : 1 < n) :
    (riemannZeta (n : ℂ)).re = ∑' k : ℕ, 1 / (((k+1 : ℕ) : ℝ) ^ n) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (n : ℂ))]
  · have hs : Summable (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ) ^ n)) :=
      tail_summable 1 n (by norm_num) hn
    have hsum :
        (∑' k : ℕ, 1 / ((k : ℂ) + 1) ^ (n : ℂ)) =
          ∑' k : ℕ, (1 / (((k+1 : ℕ) : ℝ) ^ n) : ℂ) := by
      apply tsum_congr
      intro k
      exact zeta_term_conv k n
    have hsumRe :
        (∑' k : ℕ, (1 / (((k+1 : ℕ) : ℝ) ^ n) : ℂ)).re =
          ∑' k : ℕ, 1 / (((k+1 : ℕ) : ℝ) ^ n) := by
      simpa using congrArg Complex.re
        ((Complex.ofReal_tsum (L := ⟨Filter.atTop⟩)
          (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ) ^ n))).symm)
    rw [hsum]
    exact hsumRe
  · simp [hn]

lemma zeta_re_eq_one_add_tail (n : ℕ) (hn : 1 < n) :
    (riemannZeta (n : ℂ)).re = 1 + ∑' k : ℕ, 1 / (((k+2 : ℕ) : ℝ) ^ n) := by
  rw [zeta_re_eq_tsum n hn]
  have hs : Summable (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ) ^ n)) :=
    tail_summable 1 n (by norm_num) hn
  rw [hs.tsum_eq_zero_add]
  congr <;> norm_num

noncomputable def S114 (n : ℕ) : ℝ :=
  1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n

noncomputable def U114 (n : ℕ) : ℝ :=
  1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (4:ℝ)^n + 1 / (5:ℝ)^n + 1 / (6:ℝ)^n +
  1 / (7:ℝ)^n + 1 / (8:ℝ)^n + 1 / (9:ℝ)^n + 1 / (10:ℝ)^n

noncomputable def V114 (n : ℕ) : ℝ :=
  U114 (2*n)


set_option maxHeartbeats 800000

noncomputable def Rpoly (a b c d : ℝ) : ℝ :=
  (-4:ℝ) * a^2 * b +
  (-2:ℝ) * a * d +
  (-2:ℝ) * b * c +
  (-2:ℝ) * a^4 +
  (-4:ℝ) * a * b^2 +
  (-4:ℝ) * a^2 * c +
  (-2:ℝ) * b * d +
  (-4:ℝ) * a^3 * b +
  (-2:ℝ) * c^2 +
  (-2:ℝ) * b^3 +
  (-4:ℝ) * a^2 * d +
  (-6:ℝ) * a * b * c +
  (-2:ℝ) * a^5 +
  (-2:ℝ) * c * d +
  (-6:ℝ) * a^2 * b^2 +
  (-4:ℝ) * a^3 * c +
  (-6:ℝ) * a * b * d +
  (-4:ℝ) * b^2 * c +
  (-6:ℝ) * a^4 * b +
  (-2:ℝ) * d^2 +
  (-4:ℝ) * a * c^2 +
  (-4:ℝ) * a * b^3 +
  (-4:ℝ) * a^3 * d +
  (-10:ℝ) * a^2 * b * c +
  (-4:ℝ) * b^2 * d +
  (-2:ℝ) * a^6 +
  (-6:ℝ) * a * c * d +
  (-6:ℝ) * a^3 * b^2 +
  (-4:ℝ) * b * c^2 +
  (-6:ℝ) * a^4 * c +
  (-2:ℝ) * b^4 +
  (-8:ℝ) * a^2 * b * d +
  (-8:ℝ) * a * b^2 * c +
  (-4:ℝ) * a^5 * b +
  (-4:ℝ) * a * d^2 +
  (-6:ℝ) * a^2 * c^2 +
  (-6:ℝ) * b * c * d +
  (-6:ℝ) * a^2 * b^3 +
  (-6:ℝ) * a^4 * d +
  (-10:ℝ) * a^3 * b * c +
  (-2:ℝ) * c^3 +
  (-8:ℝ) * a * b^2 * d +
  (-2:ℝ) * a^7 +
  (-4:ℝ) * b^3 * c +
  (-8:ℝ) * a^2 * c * d +
  (-4:ℝ) * a^4 * b^2 +
  (-4:ℝ) * b * d^2 +
  (-6:ℝ) * a * b * c^2 +
  (-4:ℝ) * a^5 * c +
  (-4:ℝ) * a * b^4 +
  (-6:ℝ) * a^3 * b * d +
  (-4:ℝ) * c^2 * d +
  (-8:ℝ) * a^2 * b^2 * c +
  (-4:ℝ) * b^3 * d +
  (-2:ℝ) * a^6 * b +
  (-2:ℝ) * a^2 * d^2 +
  (-6:ℝ) * a^3 * c^2 +
  (-8:ℝ) * a * b * c * d +
  (-2:ℝ) * a^3 * b^3 +
  (-2:ℝ) * a^5 * d +
  (-2:ℝ) * b^2 * c^2 +
  (-4:ℝ) * a^4 * b * c +
  (-2:ℝ) * b^5 +
  (-4:ℝ) * c * d^2 +
  (-2:ℝ) * a * c^3 +
  (-4:ℝ) * a^2 * b^2 * d +
  (-4:ℝ) * a * b^3 * c +
  (-6:ℝ) * a^3 * c * d +
  (-2:ℝ) * a * b * d^2 +
  (-4:ℝ) * a^2 * b * c^2 +
  (-4:ℝ) * b^2 * c * d +
  (-2:ℝ) * a^6 * c +
  (-2:ℝ) * a^4 * b * d +
  (-2:ℝ) * d^3 +
  (-4:ℝ) * a * c^2 * d +
  (-2:ℝ) * a^3 * b^2 * c +
  (-2:ℝ) * a * b^3 * d +
  (-2:ℝ) * a^3 * d^2 +
  (-2:ℝ) * a^4 * c^2 +
  (-2:ℝ) * b^4 * c +
  (-2:ℝ) * a^2 * b * c * d +
  (-2:ℝ) * b^2 * d^2 +
  (-2:ℝ) * a^6 * d +
  (-2:ℝ) * a * b^2 * c^2 +
  (-2:ℝ) * a * c * d^2 +
  (-2:ℝ) * a^2 * c^3 +
  (-2:ℝ) * a^3 * b^2 * d +
  (-2:ℝ) * a^4 * c * d +
  (-2:ℝ) * b^4 * d +
  (-2:ℝ) * a * b^2 * c * d +
  (-2:ℝ) * a^2 * c^2 * d

noncomputable def R114 (n : ℕ) : ℝ :=
  Rpoly (1 / (2:ℝ)^n) (1 / (3:ℝ)^n) (1 / (5:ℝ)^n) (1 / (7:ℝ)^n)

lemma poly_id (a b c d : ℝ) :
  let S := a+b+c+d
  let U := a+b+a^2+c+a*b+d+a^3+b^2+a*c
  let V := a^2+b^2+a^4+c^2+(a*b)^2+d^2+a^6+b^4+(a*c)^2
  ((1+U)^2-(1+V)-S*((1+U)^2+(1+V))) = Rpoly a b c d := by
  dsimp [Rpoly]
  ring

lemma finite_num_eq_R114 (n : ℕ) :
    ((1 + U114 n)^2 - (1 + V114 n) - S114 n * ((1 + U114 n)^2 + (1 + V114 n))) = R114 n := by
  rw [show U114 n = (1 / (2:ℝ)^n) + (1 / (3:ℝ)^n) + (1 / (2:ℝ)^n)^2 + (1 / (5:ℝ)^n) +
      (1 / (2:ℝ)^n) * (1 / (3:ℝ)^n) + (1 / (7:ℝ)^n) + (1 / (2:ℝ)^n)^3 +
      (1 / (3:ℝ)^n)^2 + (1 / (2:ℝ)^n) * (1 / (5:ℝ)^n) by
    dsimp [U114]
    ring_nf
    have hpowmul (x : ℝ) (k : ℕ) : x ^ (n * k) = (x ^ k) ^ n := by rw [mul_comm n k, pow_mul]
    simp_rw [hpowmul]
    simp_rw [← mul_pow]
    norm_num
    ring]
  rw [show V114 n = (1 / (2:ℝ)^n)^2 + (1 / (3:ℝ)^n)^2 + (1 / (2:ℝ)^n)^4 + (1 / (5:ℝ)^n)^2 +
      ((1 / (2:ℝ)^n) * (1 / (3:ℝ)^n))^2 + (1 / (7:ℝ)^n)^2 + (1 / (2:ℝ)^n)^6 +
      (1 / (3:ℝ)^n)^4 + ((1 / (2:ℝ)^n) * (1 / (5:ℝ)^n))^2 by
    dsimp [V114, U114]
    ring_nf
    have hpowmul (x : ℝ) (k : ℕ) : x ^ (n * k) = (x ^ k) ^ n := by rw [mul_comm n k, pow_mul]
    simp_rw [hpowmul]
    simp_rw [← mul_pow]
    norm_num
    ring]
  rw [show S114 n = (1 / (2:ℝ)^n) + (1 / (3:ℝ)^n) + (1 / (5:ℝ)^n) + (1 / (7:ℝ)^n) by rfl]
  exact poly_id (1 / (2:ℝ)^n) (1 / (3:ℝ)^n) (1 / (5:ℝ)^n) (1 / (7:ℝ)^n)

lemma coeff_inv_pow_bigO (c : ℝ) (b : ℕ) (hb : 11 ≤ b) :
    (fun n : ℕ => c * (1 / (b:ℝ)^n)) =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  exact (inv_pow_base_bigO (b:ℝ) (11:ℝ) (by positivity) (by norm_num) (by exact_mod_cast hb)).const_mul_left c


lemma coeff_monomial_bigO (c : ℝ) (i j k l : ℕ) (hbase : 11 ≤ 2^i * 3^j * 5^k * 7^l) :
    (fun n : ℕ => c * (1 / (2:ℝ)^n)^i * (1 / (3:ℝ)^n)^j * (1 / (5:ℝ)^n)^k * (1 / (7:ℝ)^n)^l)
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  refine (coeff_inv_pow_bigO c (2^i * 3^j * 5^k * 7^l) hbase).congr_left ?_
  intro n
  simp only [one_div, inv_pow]
  norm_cast
  ring_nf
  norm_num [Nat.cast_mul]
  ring

lemma R114_bigO : R114 =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  have h := (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((coeff_monomial_bigO (-4:ℝ) 2 1 0 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 0 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 1 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 4 0 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 2 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 2 0 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 1 0 1 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 3 1 0 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 0 2 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 3 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 2 0 0 1 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 1 1 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 5 0 0 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 0 1 1 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 2 2 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 3 0 1 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 1 1 0 1 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 2 1 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 4 1 0 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 0 0 2 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 0 2 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 3 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 3 0 0 1 (by norm_num))).add (coeff_monomial_bigO (-10:ℝ) 2 1 1 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 2 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 6 0 0 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 1 0 1 1 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 3 2 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 1 2 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 4 0 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 4 0 0 (by norm_num))).add (coeff_monomial_bigO (-8:ℝ) 2 1 0 1 (by norm_num))).add (coeff_monomial_bigO (-8:ℝ) 1 2 1 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 5 1 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 0 0 2 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 2 0 2 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 0 1 1 1 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 2 3 0 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 4 0 0 1 (by norm_num))).add (coeff_monomial_bigO (-10:ℝ) 3 1 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 0 3 0 (by norm_num))).add (coeff_monomial_bigO (-8:ℝ) 1 2 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 7 0 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 3 1 0 (by norm_num))).add (coeff_monomial_bigO (-8:ℝ) 2 0 1 1 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 4 2 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 1 0 2 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 1 1 2 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 5 0 1 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 4 0 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 3 1 0 1 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 0 2 1 (by norm_num))).add (coeff_monomial_bigO (-8:ℝ) 2 2 1 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 3 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 6 1 0 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 2 0 0 2 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 3 0 2 0 (by norm_num))).add (coeff_monomial_bigO (-8:ℝ) 1 1 1 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 3 3 0 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 5 0 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 2 2 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 4 1 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 5 0 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 0 1 2 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 0 3 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 2 2 0 1 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 3 1 0 (by norm_num))).add (coeff_monomial_bigO (-6:ℝ) 3 0 1 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 1 0 2 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 2 1 2 0 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 0 2 1 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 6 0 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 4 1 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 0 0 3 (by norm_num))).add (coeff_monomial_bigO (-4:ℝ) 1 0 2 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 3 2 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 3 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 3 0 0 2 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 4 0 2 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 4 1 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 2 1 1 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 2 0 2 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 6 0 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 2 2 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 0 1 2 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 2 0 3 0 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 3 2 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 4 0 1 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 0 4 0 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 1 2 1 1 (by norm_num))).add (coeff_monomial_bigO (-2:ℝ) 2 0 2 1 (by norm_num))
  exact h.congr_left (fun n => by
    dsimp [R114, Rpoly]
    simp only [pow_zero, pow_one, mul_one])


lemma inv_nat_pow_tendsto_zero (b : ℕ) (hb : 1 < b) :
    Tendsto (fun n : ℕ => 1 / (b:ℝ)^n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1:ℝ) / b)^n) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_
    · positivity
    · rw [div_lt_one₀]
      · exact_mod_cast hb
      · positivity
  convert h using 1
  funext n
  rw [one_div_pow]

lemma S114_tendsto_zero : Tendsto S114 atTop (𝓝 0) := by
  have h := (((inv_nat_pow_tendsto_zero 2 (by norm_num)).add
    (inv_nat_pow_tendsto_zero 3 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 5 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 7 (by norm_num))
  have h' : Tendsto (fun x => 1 / (2:ℝ)^x + 1 / (3:ℝ)^x + 1 / (5:ℝ)^x + 1 / (7:ℝ)^x) atTop (𝓝 0) := by
    simpa using h
  exact h'.congr' (Eventually.of_forall (by intro n; simp [S114]))

lemma U114_tendsto_zero : Tendsto U114 atTop (𝓝 0) := by
  have h := ((((((((inv_nat_pow_tendsto_zero 2 (by norm_num)).add
    (inv_nat_pow_tendsto_zero 3 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 4 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 5 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 6 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 7 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 8 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 9 (by norm_num))).add
    (inv_nat_pow_tendsto_zero 10 (by norm_num))
  have h' : Tendsto (fun x => 1 / (2:ℝ)^x + 1 / (3:ℝ)^x + 1 / (4:ℝ)^x + 1 / (5:ℝ)^x + 1 / (6:ℝ)^x +
      1 / (7:ℝ)^x + 1 / (8:ℝ)^x + 1 / (9:ℝ)^x + 1 / (10:ℝ)^x) atTop (𝓝 0) := by
    simpa [add_assoc] using h
  exact h'.congr' (Eventually.of_forall (by intro n; simp [U114]))

lemma V114_tendsto_zero : Tendsto V114 atTop (𝓝 0) := by
  unfold V114
  exact U114_tendsto_zero.comp (tendsto_atTop_mono (fun n : ℕ => show n ≤ 2*n by omega) (tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop))

lemma ztail_eq_U_tail (n : ℕ) (hn : 1 < n) :
    (∑' k : ℕ, 1 / (((k+2 : ℕ) : ℝ) ^ n)) =
      U114 n + ∑' k : ℕ, 1 / (((k+11 : ℕ) : ℝ) ^ n) := by
  let f : ℕ → ℝ := fun k => 1 / (((k+2 : ℕ) : ℝ) ^ n)
  have hf : Summable f := tail_summable 2 n (by norm_num) hn
  have hsplit := (hf.sum_add_tsum_nat_add 9).symm
  change (∑' k : ℕ, f k) = U114 n + ∑' k : ℕ, 1 / (((k+11 : ℕ) : ℝ) ^ n)
  rw [hsplit]
  congr 1
  · simp [f, U114, Finset.sum_range_succ]
    ring


lemma zeta_sub_one_sub_U_bigO :
    (fun n : ℕ => (riemannZeta (n : ℂ)).re - 1 - U114 n) =O[atTop]
      (fun n : ℕ => 1 / (11:ℝ)^n) := by
  refine (tail_tsum_bigO 11 (by norm_num) (by norm_num)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with n hn0
  have hn : 1 < n := by omega
  rw [zeta_re_eq_one_add_tail n hn, ztail_eq_U_tail n hn]
  ring

lemma zeta_two_mul_sub_one_sub_V_bigO :
    (fun n : ℕ => (riemannZeta (2 * (n : ℂ))).re - 1 - V114 n) =O[atTop]
      (fun n : ℕ => 1 / (11:ℝ)^n) := by
  have htail2 :
      (fun n : ℕ => ∑' k : ℕ, 1 / (((k+11 : ℕ) : ℝ) ^ (2*n))) =O[atTop]
        (fun n : ℕ => 1 / (11:ℝ)^n) := by
    refine isBigO_iff.2 ⟨tailConst 11, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnon : 0 ≤ ∑' k : ℕ, 1 / (((k+11 : ℕ) : ℝ) ^ (2*n)) := by
      apply tsum_nonneg; intro k; positivity
    have hle := tail_bound 11 (2*n) (by norm_num) (by omega)
    have hpow : 1 / (11:ℝ)^(2*n) ≤ 1 / (11:ℝ)^n := by
      have hbase : (1:ℝ) ≤ (11:ℝ)^n := by
        simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 11) n
      have hpowle : (11:ℝ)^n ≤ (11:ℝ)^(2*n) := by
        calc
          (11:ℝ)^n = (11:ℝ)^n * 1 := by ring
          _ ≤ (11:ℝ)^n * (11:ℝ)^n := mul_le_mul_of_nonneg_left hbase (by positivity)
          _ = (11:ℝ)^(2*n) := by rw [← pow_add]; congr 1; omega
      exact one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ)<11) n) hpowle
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hnon, abs_of_pos (one_div_pos.mpr (pow_pos (by norm_num : (0:ℝ)<11) n))]
    exact hle.trans (mul_le_mul_of_nonneg_left hpow (by unfold tailConst; positivity))
  refine htail2.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn2 : 1 < 2*n := by omega
  rw [show (riemannZeta (2 * (n : ℂ))).re = (riemannZeta ((2*n : ℕ) : ℂ)).re by
    congr 1; norm_num [Nat.cast_mul]]
  rw [zeta_re_eq_one_add_tail (2*n) hn2, ztail_eq_U_tail (2*n) hn2]
  dsimp [V114]
  ring

lemma zeta_re_tendsto_one : Tendsto (fun n : ℕ => (riemannZeta (n : ℂ)).re) atTop (𝓝 1) := by
  have hg : Tendsto (fun n : ℕ => 1 / (11:ℝ)^n) atTop (𝓝 0) := inv_nat_pow_tendsto_zero 11 (by norm_num)
  have he : Tendsto (fun n : ℕ => (riemannZeta (n : ℂ)).re - 1 - U114 n) atTop (𝓝 0) :=
    zeta_sub_one_sub_U_bigO.trans_tendsto hg
  have hU := U114_tendsto_zero
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h : Tendsto (fun x : ℕ => (riemannZeta (x : ℂ)).re - 1 - U114 x + U114 x + 1) atTop (𝓝 1) := by
    simpa using (he.add hU).add hc
  exact h.congr' (Eventually.of_forall (by intro n; ring))

lemma zeta_two_re_tendsto_one : Tendsto (fun n : ℕ => (riemannZeta (2 * (n : ℂ))).re) atTop (𝓝 1) := by
  have hg : Tendsto (fun n : ℕ => 1 / (11:ℝ)^n) atTop (𝓝 0) := inv_nat_pow_tendsto_zero 11 (by norm_num)
  have he : Tendsto (fun n : ℕ => (riemannZeta (2 * (n : ℂ))).re - 1 - V114 n) atTop (𝓝 0) :=
    zeta_two_mul_sub_one_sub_V_bigO.trans_tendsto hg
  have hV := V114_tendsto_zero
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h : Tendsto (fun x : ℕ => (riemannZeta (2 * (x : ℂ))).re - 1 - V114 x + V114 x + 1) atTop (𝓝 1) := by
    simpa using (he.add hV).add hc
  exact h.congr' (Eventually.of_forall (by intro n; ring))


/--
A114362 Conjecture: (1 - t(n))/(1 + t(n)) = 1/2^n + 1/3^n + 1/5^n + 1/7^n + O(1/11^n),
where t(n) = zeta(2n)/zeta(n)^2. Cf. A348829.
This is formalized as the difference between the LHS and the sum of the first four inverse prime powers
being $O(1/11^n)$ as $n \to \infty$.

-/
theorem oeis_A114362_conjecture_1 :
    (fun n : ℕ => (1 - A114362_t n) / (1 + A114362_t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  let g : ℕ → ℝ := fun n => 1 / (11:ℝ)^n
  let z₁ : ℕ → ℝ := fun n => (riemannZeta (n : ℂ)).re
  let z₂ : ℕ → ℝ := fun n => (riemannZeta (2 * (n : ℂ))).re
  have hA : (fun n => z₁ n - (1 + U114 n)) =O[atTop] g := by
    simpa [z₁, g] using zeta_sub_one_sub_U_bigO.congr_left (fun n => by ring)
  have hB : (fun n => z₂ n - (1 + V114 n)) =O[atTop] g := by
    simpa [z₂, g] using zeta_two_mul_sub_one_sub_V_bigO.congr_left (fun n => by ring)
  have hz₁_tend : Tendsto z₁ atTop (𝓝 1) := by simpa [z₁] using zeta_re_tendsto_one
  have hz₂_tend : Tendsto z₂ atTop (𝓝 1) := by simpa [z₂] using zeta_two_re_tendsto_one
  have hOneU_tend : Tendsto (fun n => 1 + U114 n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add U114_tendsto_zero : Tendsto (fun n : ℕ => (1:ℝ) + U114 n) atTop (𝓝 (1+0)))
  have hfactor : (fun n => z₁ n + (1 + U114 n)) =O[atTop] (fun _ : ℕ => (1:ℝ)) := by
    exact ((hz₁_tend.add hOneU_tend).isBigO_one ℝ)
  have hSqDiff : (fun n => z₁ n ^ 2 - (1 + U114 n)^2) =O[atTop] g := by
    have hm := hA.mul hfactor
    refine hm.congr' ?_ ?_
    · exact Eventually.of_forall (fun n => by ring)
    · exact Eventually.of_forall (fun n => by simp [g])
  have hSbd : S114 =O[atTop] (fun _ : ℕ => (1:ℝ)) := S114_tendsto_zero.isBigO_one ℝ
  have hErrBase :
      (fun n => (z₁ n ^ 2 - (1 + U114 n)^2) + (z₂ n - (1 + V114 n))) =O[atTop] g :=
    hSqDiff.add hB
  have hSErr : (fun n => S114 n * ((z₁ n ^ 2 - (1 + U114 n)^2) + (z₂ n - (1 + V114 n)))) =O[atTop] g := by
    have hm := hSbd.mul hErrBase
    refine hm.congr_right ?_
    intro n
    simp [g]
  have hErr :
      (fun n => ((z₁ n ^ 2 - z₂ n - S114 n * (z₁ n ^ 2 + z₂ n)) -
        (((1 + U114 n)^2 - (1 + V114 n) - S114 n * ((1 + U114 n)^2 + (1 + V114 n)))))) =O[atTop] g := by
    have htmp := (hSqDiff.sub hB).sub hSErr
    refine htmp.congr_left ?_
    intro n
    ring
  have hP :
      (fun n => ((1 + U114 n)^2 - (1 + V114 n) - S114 n * ((1 + U114 n)^2 + (1 + V114 n)))) =O[atTop] g := by
    exact R114_bigO.congr_left (fun n => (finite_num_eq_R114 n).symm) |>.congr_right (fun n => by simp [g])
  have hNum :
      (fun n => z₁ n ^ 2 - z₂ n - S114 n * (z₁ n ^ 2 + z₂ n)) =O[atTop] g := by
    have h := hErr.add hP
    refine h.congr_left ?_
    intro n
    ring
  let D : ℕ → ℝ := fun n => z₁ n ^ 2 + z₂ n
  have hD_tend : Tendsto D atTop (𝓝 2) := by
    have hsq : Tendsto (fun n => z₁ n ^ 2) atTop (𝓝 (1^2 : ℝ)) := hz₁_tend.pow 2
    simpa [D, show (1:ℝ) + 1 = 2 by norm_num] using hsq.add hz₂_tend
  have hDinvO : (fun n => (D n)⁻¹) =O[atTop] (fun _ : ℕ => (1:ℝ)) :=
    ((hD_tend.inv₀ (by norm_num : (2:ℝ) ≠ 0)).isBigO_one ℝ)
  have hQuot : (fun n => (z₁ n ^ 2 - z₂ n - S114 n * (z₁ n ^ 2 + z₂ n)) * (D n)⁻¹) =O[atTop] g := by
    have hm := hNum.mul hDinvO
    refine hm.congr_right ?_
    intro n
    simp [g]
  refine hQuot.congr' ?_ EventuallyEq.rfl
  have hz₁_ne : ∀ᶠ n in atTop, z₁ n ≠ 0 := hz₁_tend.eventually_ne (by norm_num : (1:ℝ) ≠ 0)
  have hD_ne : ∀ᶠ n in atTop, D n ≠ 0 := hD_tend.eventually_ne (by norm_num : (2:ℝ) ≠ 0)
  filter_upwards [hz₁_ne, hD_ne] with n hz₁n hDn
  change (z₁ n ^ 2 - z₂ n - S114 n * (z₁ n ^ 2 + z₂ n)) * (D n)⁻¹ =
    (1 - z₂ n / (z₁ n)^2) / (1 + z₂ n / (z₁ n)^2) - S114 n
  have hzsq : (z₁ n)^2 ≠ 0 := pow_ne_zero 2 hz₁n
  field_simp [D, hz₁n, hzsq, hDn]
  ring
