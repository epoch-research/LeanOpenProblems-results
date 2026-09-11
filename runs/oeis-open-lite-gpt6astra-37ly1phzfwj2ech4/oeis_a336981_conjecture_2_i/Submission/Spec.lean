import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
The coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$ T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i $$
-/
def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    -- The multinomial coefficient $\binom{k}{i, i, k-2i}$
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    -- Powers of b and c
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/--
A336981: $$a(n) = \frac{\sum_{k=0}^{n-1} (4290k + 367) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)}{n \cdot \binom{2n-1}{n-1}}$$
where $T_k(b, c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
The sequence is defined as a function $\mathbb{N} \to \mathbb{Q}$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

-- Definition for t(k) for the infinite sum
/--
$$t(k) = \frac{4290k+367}{3136^k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)$$
-/
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

/-
An elementary integral proof.  The binomial series and cosine moments turn the sum
into a double integral.  A rational divergence certificate reduces this integral
to a boundary flux, evaluated using the cosine kernel and a uniform error bound.
-/
set_option maxHeartbeats 1000000

namespace SunProof
open Real intervalIntegral

lemma cb_rec (n : ℕ) : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
    2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

lemma cos_even_integral (n : ℕ) :
    (∫ x : ℝ in 0..Real.pi, Real.cos x ^ (2 * n)) =
      Real.pi * (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, integral_cos_pow]
    simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_self, zero_div, zero_add, ih]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    rw [pow_succ]
    push_cast
    field_simp
    nlinarith [cb_rec n]

lemma cos_odd_integral (n : ℕ) :
    (∫ x : ℝ in 0..Real.pi, Real.cos x ^ (2 * n + 1)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, integral_cos_pow]
    simp [ih]

lemma multichoose_rec (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.multichoose a (n + 1) =
      (a + n) * Ring.multichoose a n := by
  have h0 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a (n + 1)
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h0 h1
  rw [ascPochhammer_succ_eval, ← h0, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  nlinarith [h1]

lemma half_multichoose (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := multichoose_rec (1 / 2 : ℝ) n
    rw [ih] at h
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    rw [pow_succ]
    apply (eq_div_iff (by positivity)).mpr
    have hh := cb_rec n
    field_simp at h
    nlinarith [h, hh]

lemma hasSum_cb (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => (Nat.centralBinom n : ℝ) / 4 ^ n * x ^ n)
      (1 / Real.sqrt (1 - x)) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum
    (y := x) (by simpa [enorm_eq_nnnorm] using hx)
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h
  simp_rw [← Ring.multichoose_eq, half_multichoose, ← Real.sqrt_eq_rpow] at h
  exact h

lemma three_half_multichoose (n : ℕ) :
    Ring.multichoose (3 / 2 : ℝ) n =
      (2 * n + 1) * (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := multichoose_rec (3 / 2 : ℝ) n
    rw [ih] at h
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    rw [pow_succ]
    push_cast
    apply (eq_div_iff (by positivity)).mpr
    have hh := cb_rec n
    field_simp at h
    apply (mul_left_cancel₀ hn)
    linear_combination 2 * h - (2 * (n : ℝ) + 3) * hh

lemma hasSum_cb_weighted (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => (4290 * n + 367) *
        (Nat.centralBinom n : ℝ) / 4 ^ n * x ^ n)
      ((2145 - 1778 * (1 - x)) / ((1 - x) * Real.sqrt (1 - x))) := by
  have h0 := hasSum_cb x hx
  have h1 := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (3 / 2)).hasSum
    (y := x) (by simpa [enorm_eq_nnnorm] using hx)
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h1
  simp_rw [← Ring.multichoose_eq, three_half_multichoose] at h1
  have hp : 0 < 1 - x := by have := (abs_lt.mp hx).2; linarith
  have he : (1 - x) ^ (3 / 2 : ℝ) = (1 - x) * Real.sqrt (1 - x) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hp, Real.rpow_one]
  rw [he] at h1
  convert (h1.mul_left 2145).sub (h0.mul_left 1778) using 1
  · ext n; ring
  · field_simp

lemma sum_even_terms (n : ℕ) (f : ℕ → ℝ) (hodd : ∀ i, f (2 * i + 1) = 0) :
    ∑ j ∈ range (n + 1), f j = ∑ i ∈ range (n / 2 + 1), f (2 * i) := by
  classical
  calc
    ∑ j ∈ range (n + 1), f j = ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = 0), f j := by
      symm
      apply sum_subset (filter_subset _ _)
      intro j hj hjf
      have hmod := Nat.mod_two_eq_zero_or_one j
      have ho : j % 2 = 1 := by simp only [mem_filter, hj, true_and] at hjf; omega
      rw [show j = 2 * (j / 2) + 1 by omega]
      exact hodd _
    _ = ∑ i ∈ range (n / 2 + 1), f (2 * i) := by
      symm
      apply sum_bij (fun i _ => 2 * i)
      · intro i hi
        simp only [mem_filter, mem_range] at *
        omega
      · intro i hi j hj hij; omega
      · intro j hj
        simp only [mem_filter, mem_range] at hj
        refine ⟨j / 2, ?_, ?_⟩
        · simp only [mem_range]; omega
        · omega
      · intro i hi; rfl

lemma trinomial_cos_moment (n : ℕ) (b d : ℤ) :
    (∫ x : ℝ in 0..Real.pi, ((b : ℝ) + 2 * d * Real.cos x) ^ n) =
      Real.pi * (T_k n b (d ^ 2) : ℝ) := by
  have hex (x : ℝ) : ((b : ℝ) + 2 * d * Real.cos x) ^ n =
      ∑ j ∈ range (n + 1), ((2 * (d : ℝ)) ^ j * (b : ℝ) ^ (n - j) * (n.choose j : ℝ)) * Real.cos x ^ j := by
    rw [add_comm, add_pow]
    apply sum_congr rfl
    intro j hj
    rw [mul_pow]
    ring
  simp_rw [hex]
  rw [integral_finset_sum (fun j hj => by apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [integral_const_mul]
  rw [sum_even_terms n _ (by intro i; rw [cos_odd_integral]; ring)]
  simp_rw [cos_even_integral]
  unfold T_k
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hc : (n.choose (2 * i) : ℝ) * (Nat.centralBinom i : ℝ) =
      (n.choose i : ℝ) * ((n - i).choose i : ℝ) := by
    have he : 2 * i - i = i := by omega
    exact_mod_cast (by simpa [Nat.centralBinom, he] using
      (Nat.choose_mul (n := n) (k := 2 * i) (s := i) (by omega)))
  rw [pow_mul, mul_pow]
  norm_num
  rw [mul_pow]
  field_simp
  linear_combination (b : ℝ) ^ (n - 2 * i) * ((d : ℝ) ^ 2) ^ i * hc

lemma integral_tsum_of_uniform_bound {a b : ℝ} (hab : a ≤ b)
    (f : ℕ → ℝ → ℝ) (M : ℕ → ℝ)
    (hf : ∀ n, ContinuousOn (f n) (Set.Icc a b))
    (hM : Summable M) (hb : ∀ n x, x ∈ Set.Icc a b → ‖f n x‖ ≤ M n) :
    (∫ x in a..b, ∑' n, f n x) = ∑' n, ∫ x in a..b, f n x := by
  have hfi (n : ℕ) : IntervalIntegrable (f n) MeasureTheory.volume a b :=
    (by simpa [Set.uIcc_of_le hab] using hf n : ContinuousOn (f n) (Set.uIcc a b)).intervalIntegrable
  have hs : Summable (fun n => ∫ x in a..b, ‖f n x‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg hab (fun x hx => norm_nonneg _))
      (fun n => ?_) (hM.mul_left (b - a))
    calc
      (∫ x in a..b, ‖f n x‖) ≤ ∫ x in a..b, M n :=
        integral_mono_on hab (hfi n).norm (intervalIntegral.intervalIntegrable_const) (hb n)
      _ = (b - a) * M n := by simp
  simp_rw [integral_of_le hab] at hs ⊢
  symm
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => (hfi n).1) hs

lemma cosine_kernel (q : ℝ) (hq : |q| < 1) :
    (∫ x : ℝ in 0..Real.pi, 1 / (1 - q * Real.cos x)) =
      Real.pi / Real.sqrt (1 - q ^ 2) := by
  have hqc (x : ℝ) : |q * Real.cos x| < 1 := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (abs_nonneg q) (Real.abs_cos_le_one x)) hq
  have heq (x : ℝ) : 1 / (1 - q * Real.cos x) = ∑' n : ℕ, (q * Real.cos x) ^ n := by
    simpa [one_div] using (hasSum_geometric_of_abs_lt_one (hqc x)).tsum_eq.symm
  simp_rw [heq]
  rw [integral_tsum_of_uniform_bound Real.pi_pos.le _ (fun n => |q| ^ n)
    (fun n => by fun_prop) (summable_geometric_of_lt_one (abs_nonneg q) hq)
    (by intro n x hx; rw [norm_pow, Real.norm_eq_abs, abs_mul];
        exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (abs_nonneg q) (Real.abs_cos_le_one x)) n)]
  have hq2 : |q ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg q)]
    nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
  have he : HasSum (fun n : ℕ => ∫ x : ℝ in 0..Real.pi, (q * Real.cos x) ^ (2 * n))
      (Real.pi / Real.sqrt (1 - q ^ 2)) := by
    convert (hasSum_cb (q ^ 2) hq2).mul_left Real.pi using 1
    · ext n
      simp_rw [mul_pow, integral_const_mul]
      rw [cos_even_integral, pow_mul]
      ring
    · ring
  have ho : HasSum (fun n : ℕ => ∫ x : ℝ in 0..Real.pi, (q * Real.cos x) ^ (2 * n + 1)) 0 := by
    convert hasSum_zero using 1
    ext n
    simp_rw [mul_pow, integral_const_mul, cos_odd_integral, mul_zero]
  have hs := HasSum.even_add_odd
    (f := fun n : ℕ => ∫ x : ℝ in 0..Real.pi, (q * Real.cos x) ^ n) he ho
  simpa only [add_zero] using hs.tsum_eq

noncomputable def surfP (u v : ℝ) : ℝ := 273 - 17 * u - 56 * v - 8 * u * v
noncomputable def surfN (u v : ℝ) : ℝ := 840840 - 1778 * surfP u v
noncomputable def surfX (x y : ℝ) : ℝ :=
  (14 + 2 * Real.cos x) * (17 + 8 * Real.cos y) / 784
noncomputable def surfW (n : ℕ) (x y : ℝ) : ℝ :=
  (4290 * n + 367) * (Nat.centralBinom n : ℝ) / 4 ^ n * surfX x y ^ n
noncomputable def surfI (x y : ℝ) : ℝ :=
  surfN (Real.cos x) (Real.cos y) /
    (surfP (Real.cos x) (Real.cos y) * Real.sqrt (surfP (Real.cos x) (Real.cos y)))

lemma product_bounds (u v : ℝ) (hu : u ∈ Set.Icc (-1) 1) (hv : v ∈ Set.Icc (-1) 1) :
    108 ≤ (14 + 2 * u) * (17 + 8 * v) ∧ (14 + 2 * u) * (17 + 8 * v) ≤ 400 := by
  have ha : 12 ≤ 14 + 2 * u ∧ 14 + 2 * u ≤ 16 := by constructor <;> linarith [hu.1, hu.2]
  have hb : 9 ≤ 17 + 8 * v ∧ 17 + 8 * v ≤ 25 := by constructor <;> linarith [hv.1, hv.2]
  constructor
  · nlinarith [mul_le_mul ha.1 hb.1 (by norm_num : (0 : ℝ) ≤ 9) (by linarith : 0 ≤ 14 + 2 * u)]
  · nlinarith [mul_le_mul ha.2 hb.2 (by linarith : 0 ≤ 17 + 8 * v) (by norm_num : (0 : ℝ) ≤ 16)]

lemma surfP_bounds (u v : ℝ) (hu : u ∈ Set.Icc (-1) 1) (hv : v ∈ Set.Icc (-1) 1) :
    192 ≤ surfP u v ∧ surfP u v ≤ 338 := by
  have h := product_bounds u v hu hv
  unfold surfP
  constructor <;> nlinarith [h.1, h.2]

lemma surfX_bounds (x y : ℝ) : 0 ≤ surfX x y ∧ surfX x y ≤ 25 / 49 := by
  have h := product_bounds (Real.cos x) (Real.cos y)
    ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩ ⟨Real.neg_one_le_cos y, Real.cos_le_one y⟩
  unfold surfX
  constructor <;> linarith [h.1, h.2]

lemma cb_bound (n : ℕ) : (Nat.centralBinom n : ℝ) / 4 ^ n ≤ 1 := by
  have h := Nat.choose_le_two_pow (2 * n) n
  rw [pow_mul] at h
  have h' : (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast h
  exact (div_le_one (by positivity)).mpr h'

lemma surfW_bound (n : ℕ) (x y : ℝ) :
    ‖surfW n x y‖ ≤ (4290 * n + 367) * (25 / 49 : ℝ) ^ n := by
  have h := surfX_bounds x y
  have hx0 : 0 ≤ surfX x y := h.1
  have hn : 0 ≤ surfW n x y := by unfold surfW; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  unfold surfW
  calc
    (4290 * (n : ℝ) + 367) * (Nat.centralBinom n : ℝ) / 4 ^ n * surfX x y ^ n =
        (4290 * (n : ℝ) + 367) * ((Nat.centralBinom n : ℝ) / 4 ^ n) * surfX x y ^ n := by ring
    _ ≤ (4290 * (n : ℝ) + 367) * 1 * (25 / 49 : ℝ) ^ n := by
      gcongr <;> first | positivity | exact h.1 | exact h.2 | exact cb_bound n
    _ = _ := by ring

lemma surfM_summable : Summable (fun n : ℕ => (4290 * (n : ℝ) + 367) * (25 / 49 : ℝ) ^ n) := by
  have h : ‖(25 / 49 : ℝ)‖ < 1 := by norm_num
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 h).mul_left (4290 : ℝ)
  have h2 := (summable_geometric_of_norm_lt_one h).mul_left (367 : ℝ)
  convert h1.add h2 using 1
  ext n
  simp [pow_one]
  ring

lemma surfW_hasSum (x y : ℝ) : HasSum (fun n => surfW n x y) (Real.sqrt 392 * surfI x y) := by
  have hX := surfX_bounds x y
  have hp := (surfP_bounds (Real.cos x) (Real.cos y)
    ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩ ⟨Real.neg_one_le_cos y, Real.cos_le_one y⟩).1
  have he : 1 - surfX x y = surfP (Real.cos x) (Real.cos y) / 392 := by
    unfold surfX surfP
    ring
  have hh := hasSum_cb_weighted (surfX x y) (by rw [abs_of_nonneg hX.1]; linarith [hX.2])
  change HasSum (fun n => surfW n x y) _ at hh
  convert hh using 1
  rw [he, Real.sqrt_div (by linarith)]
  unfold surfI surfN
  have hs : Real.sqrt 392 ≠ 0 := by positivity
  have hs2 : Real.sqrt 392 ^ 2 = 392 := by norm_num
  have hsp : Real.sqrt (surfP (Real.cos x) (Real.cos y)) ≠ 0 := by positivity
  have hp0 : surfP (Real.cos x) (Real.cos y) ≠ 0 := by linarith
  field_simp
  nlinarith [hs2]

lemma surfW_inner (n : ℕ) (x : ℝ) :
    (∫ y in 0..Real.pi, surfW n x y) =
      (4290 * (n : ℝ) + 367) * (Nat.centralBinom n : ℝ) / 3136 ^ n *
        (14 + 2 * Real.cos x) ^ n * (Real.pi * (T_k n 17 16 : ℝ)) := by
  have he (y : ℝ) : surfW n x y =
      ((4290 * (n : ℝ) + 367) * (Nat.centralBinom n : ℝ) / 3136 ^ n *
        (14 + 2 * Real.cos x) ^ n) * (17 + 8 * Real.cos y) ^ n := by
    unfold surfW surfX
    rw [div_pow, mul_pow]
    have hh : (3136 : ℝ) ^ n = 4 ^ n * 784 ^ n := by rw [← mul_pow]; norm_num
    rw [hh]
    ring
  simp_rw [he, integral_const_mul]
  congr 1
  convert trinomial_cos_moment n 17 4 using 1; norm_num

lemma surfW_double (n : ℕ) :
    (∫ x in 0..Real.pi, ∫ y in 0..Real.pi, surfW n x y) = Real.pi ^ 2 * t n := by
  simp_rw [surfW_inner, integral_mul_const, integral_const_mul]
  have hm := trinomial_cos_moment n 14 1
  norm_num at hm
  rw [hm]
  unfold t
  dsimp
  rw [Nat.centralBinom]
  ring

lemma series_as_integral : (∑' n : ℕ, t n) =
    Real.sqrt 392 / Real.pi ^ 2 * (∫ x in 0..Real.pi, ∫ y in 0..Real.pi, surfI x y) := by
  have hinner (x : ℝ) :
      (∫ y in 0..Real.pi, ∑' n, surfW n x y) = ∑' n, ∫ y in 0..Real.pi, surfW n x y := by
    refine integral_tsum_of_uniform_bound Real.pi_pos.le _
      (fun n => (4290 * (n : ℝ) + 367) * (25 / 49 : ℝ) ^ n) ?_ surfM_summable ?_
    · intro n; unfold surfW surfX; fun_prop
    · intro n y hy; exact surfW_bound n x y
  have houter :
      (∫ x in 0..Real.pi, ∑' n, ∫ y in 0..Real.pi, surfW n x y) =
        ∑' n, ∫ x in 0..Real.pi, ∫ y in 0..Real.pi, surfW n x y := by
    refine integral_tsum_of_uniform_bound Real.pi_pos.le _
      (fun n => ((4290 * (n : ℝ) + 367) * (25 / 49 : ℝ) ^ n) * Real.pi)
      ?_ (surfM_summable.mul_right Real.pi) ?_
    · intro n; simp_rw [surfW_inner]; fun_prop
    · intro n x hx
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := Real.pi) (fun y hy => surfW_bound n x y)
      simpa [abs_of_nonneg Real.pi_pos.le] using hb
  have he : Real.sqrt 392 * (∫ x in 0..Real.pi, ∫ y in 0..Real.pi, surfI x y) =
      Real.pi ^ 2 * ∑' n : ℕ, t n := by
    calc
      _ = ∫ x in 0..Real.pi, ∫ y in 0..Real.pi, Real.sqrt 392 * surfI x y := by
        simp_rw [integral_const_mul]
      _ = ∫ x in 0..Real.pi, ∫ y in 0..Real.pi, ∑' n, surfW n x y := by
        simp_rw [(surfW_hasSum _ _).tsum_eq]
      _ = ∑' n, ∫ x in 0..Real.pi, ∫ y in 0..Real.pi, surfW n x y := by
        simp_rw [hinner]; exact houter
      _ = _ := by simp_rw [surfW_double]; exact tsum_mul_left
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith [he]
end SunProof


set_option maxHeartbeats 1000000
namespace SunProof
open Real intervalIntegral

lemma inv_sqrt_deriv {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (hp : 0 < f x) :
    HasDerivAt (fun y => 1 / Real.sqrt (f y))
      (-f' / (2 * f x * Real.sqrt (f x))) x := by
  have hs : Real.sqrt (f x) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have h := (hf.sqrt hp.ne').inv hs
  rw [Real.sq_sqrt hp.le] at h
  convert h using 1
  · ext y; simp [one_div]
  · ring

lemma neg_sin_div_sqrt_deriv (A P : ℝ → ℝ) (Ad Pd θ : ℝ)
    (hA : HasDerivAt A Ad (Real.cos θ)) (hP : HasDerivAt P Pd (Real.cos θ))
    (hp : 0 < P (Real.cos θ)) :
    HasDerivAt (fun z => -A (Real.cos z) * Real.sin z / Real.sqrt (P (Real.cos z)))
      (((1 - Real.cos θ ^ 2) * P (Real.cos θ) * Ad -
        Real.cos θ * P (Real.cos θ) * A (Real.cos θ) -
        (1 - Real.cos θ ^ 2) * Pd * A (Real.cos θ) / 2) /
        (P (Real.cos θ) * Real.sqrt (P (Real.cos θ)))) θ := by
  have hi := (inv_sqrt_deriv hP hp).comp θ (Real.hasDerivAt_cos θ)
  have ha := hA.comp θ (Real.hasDerivAt_cos θ)
  have h := ((ha.neg.mul (Real.hasDerivAt_sin θ)).mul hi)
  dsimp only [Function.comp_apply, Pi.mul_apply, Pi.neg_apply] at h
  convert h using 1
  · ext z; simp only [Function.comp_apply, Pi.mul_apply, Pi.neg_apply]; ring
  · have hp0 := hp.ne'
    have hs0 : Real.sqrt (P (Real.cos θ)) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    field_simp
    rw [Real.sin_sq]; ring

syntax "diff_poly" : tactic
macro_rules
| `(tactic| diff_poly) => `(tactic|
  first
  | exact hasDerivAt_id _
  | exact hasDerivAt_const _ _
  | (apply HasDerivAt.add <;> diff_poly)
  | (apply HasDerivAt.sub <;> diff_poly)
  | (apply HasDerivAt.mul <;> diff_poly)
  | (apply HasDerivAt.neg <;> diff_poly)
  | (apply HasDerivAt.pow <;> diff_poly))

noncomputable def curveOne (u v : ℝ) : ℝ :=
  u * v - u - v - 3

noncomputable def curveTwo (u v : ℝ) : ℝ :=
  8 * u ^ 2 * v + 17 * u ^ 2 + 48 * u * v + 222 * u - 56 * v + 785

noncomputable def curveFour (u v : ℝ) : ℝ :=
  u ^ 2 + 48 * u * v - 2 * u - 48 * v + 577

noncomputable def aNum (u v : ℝ) : ℝ :=
  14 * (96 * u ^ 4 * v ^ 3 - 620 * u ^ 4 * v ^ 2 - 398 * u ^ 4 * v + 7797 * u ^ 4 - 39168 * u ^ 3 * v ^ 3 - 13616 * u ^ 3 * v ^ 2 + 353464 * u ^ 3 * v + 82020 * u ^ 3 - 199488 * u ^ 2 * v ^ 3 - 2032104 * u ^ 2 * v ^ 2 + 4349228 * u ^ 2 * v + 4797654 * u ^ 2 + 516096 * u * v ^ 3 - 11793136 * u * v ^ 2 - 6433352 * u * v + 61946196 * u - 277536 * v ^ 3 + 13839476 * v ^ 2 - 145872398 * v + 223949565)

noncomputable def bNum (u v : ℝ) : ℝ :=
  7 * (192 * u ^ 5 * v ^ 2 - 1984 * u ^ 5 * v - 5083 * u ^ 5 - 113856 * u ^ 4 * v ^ 2 - 244576 * u ^ 4 * v - 5593 * u ^ 4 - 787584 * u ^ 3 * v ^ 2 - 2434560 * u ^ 3 * v - 2247566 * u ^ 3 + 4309632 * u ^ 2 * v ^ 2 - 5082176 * u ^ 2 * v - 13447090 * u ^ 2 - 5802048 * u * v ^ 2 + 82058944 * u * v + 56933561 * u + 2393664 * v ^ 2 - 74295648 * v + 549185595)

noncomputable def aNumU (u v : ℝ) : ℝ :=
  56 * (96 * u ^ 3 * v ^ 3 - 620 * u ^ 3 * v ^ 2 - 398 * u ^ 3 * v + 7797 * u ^ 3 - 29376 * u ^ 2 * v ^ 3 - 10212 * u ^ 2 * v ^ 2 + 265098 * u ^ 2 * v + 61515 * u ^ 2 - 99744 * u * v ^ 3 - 1016052 * u * v ^ 2 + 2174614 * u * v + 2398827 * u + 129024 * v ^ 3 - 2948284 * v ^ 2 - 1608338 * v + 15486549)

noncomputable def bNumV (u v : ℝ) : ℝ :=
  224 * (u - 1) * (12 * u ^ 4 * v - 62 * u ^ 4 - 7104 * u ^ 3 * v - 7705 * u ^ 3 - 56328 * u ^ 2 * v - 83785 * u ^ 2 + 213024 * u * v - 242603 * u - 149604 * v + 2321739)

noncomputable def rDenU (u v : ℝ) : ℝ :=
  40 * u ^ 4 * v ^ 2 + 45 * u ^ 4 * v - 85 * u ^ 4 + 1536 * u ^ 3 * v ^ 3 + 1824 * u ^ 3 * v ^ 2 - 2804 * u ^ 3 * v - 956 * u ^ 3 + 4608 * u ^ 2 * v ^ 3 + 31152 * u ^ 2 * v ^ 2 - 20658 * u ^ 2 * v - 32142 * u ^ 2 - 13824 * u * v ^ 3 + 79520 * u * v ^ 2 + 37260 * u * v - 313948 * u + 7680 * v ^ 3 - 112536 * v ^ 2 + 231917 * v - 832517

noncomputable def rDenV (u v : ℝ) : ℝ :=
  (u - 1) * (16 * u ^ 4 * v + 9 * u ^ 4 + 1152 * u ^ 3 * v ^ 2 + 928 * u ^ 3 * v - 692 * u ^ 3 + 5760 * u ^ 2 * v ^ 2 + 21696 * u ^ 2 * v - 7578 * u ^ 2 - 14976 * u * v ^ 2 + 101216 * u * v + 11052 * u + 8064 * v ^ 2 - 123856 * v + 242969)

noncomputable def rDen (u v : ℝ) : ℝ := curveOne u v * curveTwo u v * curveFour u v
noncomputable def certA (u v : ℝ) : ℝ := aNum u v / rDen u v
noncomputable def certB (u v : ℝ) : ℝ := bNum u v / rDen u v
noncomputable def certAU (u v : ℝ) : ℝ :=
  (aNumU u v * rDen u v - aNum u v * rDenU u v) / rDen u v ^ 2
noncomputable def certBV (u v : ℝ) : ℝ :=
  (bNumV u v * rDen u v - bNum u v * rDenV u v) / rDen u v ^ 2

lemma aNum_u_deriv (u v : ℝ) : HasDerivAt (fun u => aNum u v) (aNumU u v) u := by
  convert (show HasDerivAt (fun u => aNum u v) _ u from by
    unfold aNum 
    diff_poly) using 1
  unfold aNumU
  try simp only [npowRec]
  ring

lemma bNum_v_deriv (u v : ℝ) : HasDerivAt (fun v => bNum u v) (bNumV u v) v := by
  convert (show HasDerivAt (fun v => bNum u v) _ v from by
    unfold bNum 
    diff_poly) using 1
  unfold bNumV
  try simp only [npowRec]
  ring

lemma rDen_u_deriv (u v : ℝ) : HasDerivAt (fun u => rDen u v) (rDenU u v) u := by
  convert (show HasDerivAt (fun u => rDen u v) _ u from by
    unfold rDen curveOne curveTwo curveFour
    diff_poly) using 1
  unfold rDenU
  try simp only [npowRec]
  ring

lemma rDen_v_deriv (u v : ℝ) : HasDerivAt (fun v => rDen u v) (rDenV u v) v := by
  convert (show HasDerivAt (fun v => rDen u v) _ v from by
    unfold rDen curveOne curveTwo curveFour
    diff_poly) using 1
  unfold rDenV
  try simp only [npowRec]
  ring

lemma certA_deriv (u v : ℝ) (hr : rDen u v ≠ 0) :
    HasDerivAt (fun u => certA u v) (certAU u v) u :=
  (aNum_u_deriv u v).div (rDen_u_deriv u v) hr

lemma certB_deriv (u v : ℝ) (hr : rDen u v ≠ 0) :
    HasDerivAt (fun v => certB u v) (certBV u v) v :=
  (bNum_v_deriv u v).div (rDen_v_deriv u v) hr

lemma divergence_certificate (u v : ℝ) (hr : rDen u v ≠ 0) :
    (1 - u ^ 2) * surfP u v * certAU u v - u * surfP u v * certA u v -
      (1 - u ^ 2) * (-17 - 8 * v) * certA u v / 2 +
    ((1 - v ^ 2) * surfP u v * certBV u v - v * surfP u v * certB u v -
      (1 - v ^ 2) * (-56 - 8 * u) * certB u v / 2) = surfN u v := by
  unfold certAU certBV certA certB
  field_simp
  unfold aNum bNum aNumU bNumV rDen rDenU rDenV curveOne curveTwo curveFour surfN surfP
  ring

lemma certA_partial (u v : ℝ) (hu : u ≠ 1) (h1 : curveOne u v ≠ 0)
    (h2 : curveTwo u v ≠ 0) (h4 : curveFour u v ≠ 0) :
    certA u v =
      -7 * (u - 49) * (u - 25) * (u + 23) / (2 * (u - 1) * curveFour u v) +
      (7 * u - 2891) / (2 * u - 2) -
      1470 * (3 * u + 29) * (5 * u + 27) / ((u - 1) * curveTwo u v) +
      770 * (5 * u - 21) / ((u - 1) * curveOne u v) := by
  have hum : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hu2 : 2 * u - 2 ≠ 0 := by intro h; apply hu; linarith
  unfold certA rDen
  field_simp
  unfold aNum curveOne curveTwo curveFour
  ring


lemma curveTwo_pos (u v : ℝ) (hu : u ∈ Set.Icc (-1) 1) (hv : v ∈ Set.Icc (-1) 1) :
    484 ≤ curveTwo u v := by
  have hprod : 0 ≤ (1 - u) * (u + 7) * (1 - v) := by
    apply mul_nonneg (mul_nonneg (by linarith [hu.2]) (by linarith [hu.1])) (by linarith [hv.2])
  have hs : 22 ≤ 5 * u + 27 := by linarith [hu.1]
  unfold curveTwo
  nlinarith [sq_nonneg (5 * u + 27 - 22)]

lemma curveFour_pos (u v : ℝ) (hu : u ∈ Set.Icc (-1) 1) (hv : v ∈ Set.Icc (-1) 1) :
    484 ≤ curveFour u v := by
  have hprod : 0 ≤ (1 - u) * (1 - v) := mul_nonneg (by linarith [hu.2]) (by linarith [hv.2])
  have hs : 22 ≤ u + 23 := by linarith [hu.1]
  unfold curveFour
  nlinarith [sq_nonneg (u + 23 - 22)]

lemma curveOne_neg (u v : ℝ) (hu : u ∈ Set.Ioc (-1) 1) (hv : v ∈ Set.Icc (-1) 1) :
    curveOne u v < 0 := by
  have hprod : 0 ≤ (1 - u) * (v + 1) := mul_nonneg (by linarith [hu.2]) (by linarith [hv.1])
  unfold curveOne
  nlinarith [hu.1]

lemma rDen_ne (u v : ℝ) (hu : u ∈ Set.Ioc (-1) 1) (hv : v ∈ Set.Icc (-1) 1) :
    rDen u v ≠ 0 := by
  unfold rDen
  have h1 := curveOne_neg u v hu hv
  have h2 := curveTwo_pos u v ⟨hu.1.le, hu.2⟩ hv
  have h4 := curveFour_pos u v ⟨hu.1.le, hu.2⟩ hv
  exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)

lemma surfP_u_deriv (u v : ℝ) : HasDerivAt (fun u => surfP u v) (-17 - 8 * v) u := by
  convert (show HasDerivAt (fun u => surfP u v) _ u from by unfold surfP; diff_poly) using 1
  ring

lemma surfP_v_deriv (u v : ℝ) : HasDerivAt (fun v => surfP u v) (-56 - 8 * u) v := by
  convert (show HasDerivAt (fun v => surfP u v) _ v from by unfold surfP; diff_poly) using 1
  ring

noncomputable def formU (u v : ℝ) : ℝ :=
  ((1 - u ^ 2) * surfP u v * certAU u v - u * surfP u v * certA u v -
    (1 - u ^ 2) * (-17 - 8 * v) * certA u v / 2) /
    (surfP u v * Real.sqrt (surfP u v))
noncomputable def formV (u v : ℝ) : ℝ :=
  ((1 - v ^ 2) * surfP u v * certBV u v - v * surfP u v * certB u v -
    (1 - v ^ 2) * (-56 - 8 * u) * certB u v / 2) /
    (surfP u v * Real.sqrt (surfP u v))
noncomputable def fluxU (x y : ℝ) : ℝ :=
  -certA (Real.cos x) (Real.cos y) * Real.sin x / Real.sqrt (surfP (Real.cos x) (Real.cos y))
noncomputable def fluxV (x y : ℝ) : ℝ :=
  -certB (Real.cos x) (Real.cos y) * Real.sin y / Real.sqrt (surfP (Real.cos x) (Real.cos y))

lemma forms_sum (u v : ℝ) (hr : rDen u v ≠ 0) :
    formU u v + formV u v = surfN u v / (surfP u v * Real.sqrt (surfP u v)) := by
  unfold formU formV
  rw [← add_div, divergence_certificate u v hr]

lemma fluxU_deriv (x y : ℝ) (hr : rDen (Real.cos x) (Real.cos y) ≠ 0) :
    HasDerivAt (fun x => fluxU x y) (formU (Real.cos x) (Real.cos y)) x := by
  have hp := (surfP_bounds (Real.cos x) (Real.cos y)
    ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩ ⟨Real.neg_one_le_cos y, Real.cos_le_one y⟩).1
  exact neg_sin_div_sqrt_deriv _ _ _ _ x (certA_deriv _ _ hr) (surfP_u_deriv _ _) (by linarith)

lemma fluxV_deriv (x y : ℝ) (hr : rDen (Real.cos x) (Real.cos y) ≠ 0) :
    HasDerivAt (fun y => fluxV x y) (formV (Real.cos x) (Real.cos y)) y := by
  have hp := (surfP_bounds (Real.cos x) (Real.cos y)
    ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩ ⟨Real.neg_one_le_cos y, Real.cos_le_one y⟩).1
  exact neg_sin_div_sqrt_deriv _ _ _ _ y (certB_deriv _ _ hr) (surfP_v_deriv _ _) (by linarith)

@[fun_prop] lemma aNum_continuous : Continuous (fun z : ℝ × ℝ => aNum z.1 z.2) := by
  unfold aNum
  fun_prop

@[fun_prop] lemma bNum_continuous : Continuous (fun z : ℝ × ℝ => bNum z.1 z.2) := by
  unfold bNum
  fun_prop

@[fun_prop] lemma aNumU_continuous : Continuous (fun z : ℝ × ℝ => aNumU z.1 z.2) := by
  unfold aNumU
  fun_prop

@[fun_prop] lemma bNumV_continuous : Continuous (fun z : ℝ × ℝ => bNumV z.1 z.2) := by
  unfold bNumV
  fun_prop

@[fun_prop] lemma rDenU_continuous : Continuous (fun z : ℝ × ℝ => rDenU z.1 z.2) := by
  unfold rDenU
  fun_prop

@[fun_prop] lemma rDenV_continuous : Continuous (fun z : ℝ × ℝ => rDenV z.1 z.2) := by
  unfold rDenV
  fun_prop

@[fun_prop] lemma rDen_continuous : Continuous (fun z : ℝ × ℝ => rDen z.1 z.2) := by
  unfold rDen curveOne curveTwo curveFour
  fun_prop

@[fun_prop] lemma surfP_continuous : Continuous (fun z : ℝ × ℝ => surfP z.1 z.2) := by
  unfold surfP
  fun_prop

lemma certA_continuousAt (u v : ℝ) (hr : rDen u v ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => certA z.1 z.2) (u, v) :=
  aNum_continuous.continuousAt.div rDen_continuous.continuousAt hr
lemma certB_continuousAt (u v : ℝ) (hr : rDen u v ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => certB z.1 z.2) (u, v) :=
  bNum_continuous.continuousAt.div rDen_continuous.continuousAt hr
lemma certAU_continuousAt (u v : ℝ) (hr : rDen u v ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => certAU z.1 z.2) (u, v) := by
  unfold certAU
  fun_prop (disch := positivity)
lemma certBV_continuousAt (u v : ℝ) (hr : rDen u v ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => certBV z.1 z.2) (u, v) := by
  unfold certBV
  fun_prop (disch := positivity)

lemma formU_continuousAt (u v : ℝ) (hr : rDen u v ≠ 0) (hp : 0 < surfP u v) :
    ContinuousAt (fun z : ℝ × ℝ => formU z.1 z.2) (u, v) := by
  have ha := certA_continuousAt u v hr
  have hd := certAU_continuousAt u v hr
  unfold formU
  fun_prop (disch := positivity)

lemma formV_continuousAt (u v : ℝ) (hr : rDen u v ≠ 0) (hp : 0 < surfP u v) :
    ContinuousAt (fun z : ℝ × ℝ => formV z.1 z.2) (u, v) := by
  have ha := certB_continuousAt u v hr
  have hd := certBV_continuousAt u v hr
  unfold formV
  fun_prop (disch := positivity)

@[fun_prop] lemma surfI_continuous : Continuous (fun z : ℝ × ℝ => surfI z.1 z.2) := by
  unfold surfI surfN
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    have hp := (surfP_bounds (Real.cos z.1) (Real.cos z.2)
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).1
    positivity

lemma cosine_rDen_ne (a x y : ℝ) (ha : a < Real.pi) (hx : x ∈ Set.Icc 0 a) :
    rDen (Real.cos x) (Real.cos y) ≠ 0 := by
  apply rDen_ne
  · refine ⟨?_, Real.cos_le_one _⟩
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi hx.1 (le_refl Real.pi) (lt_of_le_of_lt hx.2 ha)
  · exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

lemma formU_cos_continuous (a : ℝ) (ha : a < Real.pi) :
    ContinuousOn (fun z : ℝ × ℝ => formU (Real.cos z.1) (Real.cos z.2))
      (Set.Icc (0, 0) (a, Real.pi)) := by
  intro z hz
  have hr := cosine_rDen_ne a z.1 z.2 ha ⟨hz.1.1, hz.2.1⟩
  have hp := (surfP_bounds (Real.cos z.1) (Real.cos z.2)
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).1
  exact ((formU_continuousAt _ _ hr (by linarith)).comp (f := fun z : ℝ × ℝ => (Real.cos z.1, Real.cos z.2)) (show ContinuousAt (fun z : ℝ × ℝ => (Real.cos z.1, Real.cos z.2)) z by fun_prop)).continuousWithinAt

lemma formV_cos_continuous (a : ℝ) (ha : a < Real.pi) :
    ContinuousOn (fun z : ℝ × ℝ => formV (Real.cos z.1) (Real.cos z.2))
      (Set.Icc (0, 0) (a, Real.pi)) := by
  intro z hz
  have hr := cosine_rDen_ne a z.1 z.2 ha ⟨hz.1.1, hz.2.1⟩
  have hp := (surfP_bounds (Real.cos z.1) (Real.cos z.2)
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).1
  exact ((formV_continuousAt _ _ hr (by linarith)).comp (f := fun z : ℝ × ℝ => (Real.cos z.1, Real.cos z.2)) (show ContinuousAt (fun z : ℝ × ℝ => (Real.cos z.1, Real.cos z.2)) z by fun_prop)).continuousWithinAt

lemma rectangle_slice_y {a b c d x : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc (a, c) (b, d))) (hx : x ∈ Set.Icc a b) :
    ContinuousOn (f x) (Set.Icc c d) := by
  exact hf.comp (by fun_prop : ContinuousOn (fun y => (x, y)) (Set.Icc c d))
    (fun y hy => ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩)

lemma rectangle_slice_x {a b c d y : ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc (a, c) (b, d))) (hy : y ∈ Set.Icc c d) :
    ContinuousOn (fun x => f x y) (Set.Icc a b) := by
  exact hf.comp (by fun_prop : ContinuousOn (fun x => (x, y)) (Set.Icc a b))
    (fun x hx => ⟨⟨hx.1, hy.1⟩, ⟨hx.2, hy.2⟩⟩)

lemma rectangle_swap {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc (a, c) (b, d))) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp_rw [integral_of_le hab, integral_of_le hcd]
  apply MeasureTheory.integral_integral_swap
  rw [MeasureTheory.Measure.prod_restrict]
  exact (hf.integrableOn_Icc (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)).mono_set
    (fun z hz => ⟨⟨hz.1.1.le, hz.2.1.le⟩, ⟨hz.1.2, hz.2.2⟩⟩)

lemma divergence_integral_cut (a : ℝ) (ha0 : 0 ≤ a) (ha : a < Real.pi) :
    (∫ x in 0..a, ∫ y in 0..Real.pi, surfI x y) = ∫ y in 0..Real.pi, fluxU a y := by
  have hu := formU_cos_continuous a ha
  have hv := formV_cos_continuous a ha
  have hyU (x : ℝ) (hx : x ∈ Set.Icc 0 a) :
      IntervalIntegrable (fun y => formU (Real.cos x) (Real.cos y)) MeasureTheory.volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le Real.pi_pos.le] using rectangle_slice_y (fun x y => formU (Real.cos x) (Real.cos y)) hu hx
  have hyV (x : ℝ) (hx : x ∈ Set.Icc 0 a) :
      IntervalIntegrable (fun y => formV (Real.cos x) (Real.cos y)) MeasureTheory.volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le Real.pi_pos.le] using rectangle_slice_y (fun x y => formV (Real.cos x) (Real.cos y)) hv hx
  have hxU (y : ℝ) (hy : y ∈ Set.Icc 0 Real.pi) :
      IntervalIntegrable (fun x => formU (Real.cos x) (Real.cos y)) MeasureTheory.volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le ha0] using rectangle_slice_x (fun x y => formU (Real.cos x) (Real.cos y)) hu hy
  have hvzero (x : ℝ) (hx : x ∈ Set.Icc 0 a) :
      (∫ y in 0..Real.pi, formV (Real.cos x) (Real.cos y)) = 0 := by
    have he := integral_eq_sub_of_hasDerivAt
      (fun y hy => fluxV_deriv x y (cosine_rDen_ne a x y ha hx)) (hyV x hx)
    simpa [fluxV] using he
  calc
    _ = ∫ x in 0..a, ∫ y in 0..Real.pi, formU (Real.cos x) (Real.cos y) := by
      apply integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc 0 a := by simpa [Set.uIcc_of_le ha0] using hx
      calc
        (∫ y in 0..Real.pi, surfI x y) =
            ∫ y in 0..Real.pi, formU (Real.cos x) (Real.cos y) + formV (Real.cos x) (Real.cos y) := by
          apply integral_congr
          intro y hy
          exact (forms_sum _ _ (cosine_rDen_ne a x y ha hx')).symm
        _ = _ := by rw [integral_add (hyU x hx') (hyV x hx'), hvzero x hx', add_zero]
    _ = ∫ y in 0..Real.pi, ∫ x in 0..a, formU (Real.cos x) (Real.cos y) :=
      rectangle_swap ha0 Real.pi_pos.le _ hu
    _ = _ := by
      apply integral_congr
      intro y hy
      have hy' : y ∈ Set.Icc 0 Real.pi := by simpa [Set.uIcc_of_le Real.pi_pos.le] using hy
      have he := integral_eq_sub_of_hasDerivAt
        (fun x hx => fluxU_deriv x y (cosine_rDen_ne a x y ha (by simpa [Set.uIcc_of_le ha0] using hx)))
        (hxU y hy')
      simpa [fluxU] using he
end SunProof


set_option maxHeartbeats 1000000
namespace SunProof
open Real intervalIntegral Filter
open scoped Topology

noncomputable def kernelD (u v : ℝ) : ℝ := u + 3 + (1 - u) * v
noncomputable def kernelK (u : ℝ) : ℝ := 770 * (5 * u - 21) / (u - 1)
noncomputable def regularA (u v : ℝ) : ℝ :=
  -7 * (u - 49) * (u - 25) * (u + 23) / (2 * (u - 1) * curveFour u v) +
  (7 * u - 2891) / (2 * u - 2) -
  1470 * (3 * u + 29) * (5 * u + 27) / ((u - 1) * curveTwo u v)

lemma kernelD_pos (u v : ℝ) (hu : u ∈ Set.Ioc (-1) 0) (hv : v ∈ Set.Icc (-1) 1) :
    0 < kernelD u v := by
  have h := curveOne_neg u v ⟨hu.1, by linarith [hu.2]⟩ hv
  unfold kernelD curveOne at *
  linarith

lemma certA_split (u v : ℝ) (hu : u ∈ Set.Ioc (-1) 0) (hv : v ∈ Set.Icc (-1) 1) :
    certA u v = regularA u v - kernelK u / kernelD u v := by
  have h1 := curveOne_neg u v ⟨hu.1, by linarith [hu.2]⟩ hv
  have h2 := curveTwo_pos u v ⟨hu.1.le, by linarith [hu.2]⟩ hv
  have h4 := curveFour_pos u v ⟨hu.1.le, by linarith [hu.2]⟩ hv
  rw [certA_partial u v (by linarith [hu.2]) (by linarith) (by linarith) (by linarith)]
  have he : curveOne u v = -kernelD u v := by unfold curveOne kernelD; ring
  rw [he, mul_neg, div_neg]
  unfold regularA kernelK
  rw [div_div]
  ring

lemma sqrt_kernel_error (u v : ℝ) (hu : u ∈ Set.Icc (-1) 0) (hv : v ∈ Set.Icc (-1) 1) :
    |1 / Real.sqrt (surfP u v) - 1 / Real.sqrt 338| ≤ 64 * kernelD u v := by
  have hp := surfP_bounds u v ⟨hu.1, by linarith [hu.2]⟩ hv
  have hp1 : 1 ≤ Real.sqrt (surfP u v) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ surfP u v by linarith [hp.1])
    simpa using h
  have hc1 : 1 ≤ Real.sqrt (338 : ℝ) := by norm_num
  have hpc : Real.sqrt (surfP u v) ≤ Real.sqrt 338 := Real.sqrt_le_sqrt hp.2
  have hpn : Real.sqrt (surfP u v) ≠ 0 := by linarith
  have hcn : Real.sqrt (338 : ℝ) ≠ 0 := by positivity
  have hsqP : Real.sqrt (surfP u v) ^ 2 = surfP u v := Real.sq_sqrt (by linarith [hp.1])
  have hsqC : Real.sqrt (338 : ℝ) ^ 2 = 338 := by norm_num
  have hn : 0 ≤ 1 / Real.sqrt (surfP u v) - 1 / Real.sqrt 338 := by
    have h := one_div_le_one_div_of_le (by linarith : 0 < Real.sqrt (surfP u v)) hpc
    linarith
  rw [abs_of_nonneg hn]
  calc
    _ = (Real.sqrt 338 - Real.sqrt (surfP u v)) /
        (Real.sqrt (surfP u v) * Real.sqrt 338) := by field_simp
    _ ≤ Real.sqrt 338 - Real.sqrt (surfP u v) := by
      apply _root_.div_le_self (by linarith)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hc1)]
    _ ≤ 338 - surfP u v := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpc) (show 0 ≤ Real.sqrt 338 + Real.sqrt (surfP u v) - 1 by linarith)]
    _ ≤ 64 * kernelD u v := by
      have hm : 0 ≤ (-u) * (v + 1) := mul_nonneg (by linarith [hu.2]) (by linarith [hv.1])
      unfold surfP kernelD
      nlinarith [hu.1, hv.1]

lemma kernel_integral (u : ℝ) (hu : u ∈ Set.Ioc (-1) 0) :
    (∫ y in 0..Real.pi, 1 / kernelD u (Real.cos y)) = Real.pi / Real.sqrt (8 * (u + 1)) := by
  let q : ℝ := -(1 - u) / (u + 3)
  have ha : 0 < u + 3 := by linarith [hu.1]
  have hq : |q| < 1 := by
    have hqn : q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hu.2]) ha.le
    rw [abs_of_nonpos hqn]
    dsimp [q]
    rw [neg_div, neg_neg, div_lt_one ha]
    linarith [hu.1]
  have he (y : ℝ) : 1 / kernelD u (Real.cos y) = (1 / (u + 3)) * (1 / (1 - q * Real.cos y)) := by
    simp only [one_div, ← mul_inv]
    congr 1
    dsimp [kernelD, q]
    field_simp
    ring
  simp_rw [he, integral_const_mul]
  rw [cosine_kernel q hq]
  have hpos : 0 < 1 - q ^ 2 := by nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
  have hs : (u + 3) * Real.sqrt (1 - q ^ 2) = Real.sqrt (8 * (u + 1)) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hpos.le, Real.sq_sqrt (by linarith [hu.1])]
    dsimp [q]
    field_simp
    ring
  rw [← hs]
  simp only [div_eq_mul_inv, mul_inv]
  ring

lemma kernel_mass (u : ℝ) (hu : u ∈ Set.Ioc (-1) 0) :
    Real.sqrt (1 - u ^ 2) * (∫ y in 0..Real.pi, 1 / kernelD u (Real.cos y)) =
      Real.pi * Real.sqrt ((1 - u) / 8) := by
  rw [kernel_integral u hu]
  have hp : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have he : (1 - u ^ 2) / (8 * (u + 1)) = (1 - u) / 8 := by
    have hu0 : u + 1 ≠ 0 := by linarith [hu.1]
    field_simp
    ring
  calc
    Real.sqrt (1 - u ^ 2) * (Real.pi / Real.sqrt (8 * (u + 1))) =
        Real.pi * (Real.sqrt (1 - u ^ 2) / Real.sqrt (8 * (u + 1))) := by ring
    _ = _ := by rw [← Real.sqrt_div hp, he]

lemma regularA_uniform_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u v, u ∈ Set.Icc (-1) 0 → v ∈ Set.Icc (-1) 1 →
      |regularA u v / Real.sqrt (surfP u v)| ≤ C := by
  have hc : ContinuousOn (fun z : ℝ × ℝ => regularA z.1 z.2 / Real.sqrt (surfP z.1 z.2))
      (Set.Icc (-1, -1) (0, 1)) := by
    intro z hz
    have hu : z.1 ∈ Set.Icc (-1) 1 := ⟨hz.1.1, by linarith [hz.2.1]⟩
    have hv : z.2 ∈ Set.Icc (-1) 1 := ⟨hz.1.2, hz.2.2⟩
    have h2 := curveTwo_pos _ _ hu hv
    have h4 := curveFour_pos _ _ hu hv
    have hp := (surfP_bounds _ _ hu hv).1
    have hum : z.1 - 1 ≠ 0 := by linarith [hz.2.1]
    have hut : 2 * z.1 - 2 ≠ 0 := by linarith [hz.2.1]
    have hc2 : Continuous (fun z : ℝ × ℝ => curveTwo z.1 z.2) := by unfold curveTwo; fun_prop
    have hc4 : Continuous (fun z : ℝ × ℝ => curveFour z.1 z.2) := by unfold curveFour; fun_prop
    apply ContinuousAt.continuousWithinAt
    unfold regularA
    fun_prop (disch := positivity)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro u v hu hv
  have hh := hC (Set.mem_image_of_mem (fun z : ℝ × ℝ => ‖regularA z.1 z.2 / Real.sqrt (surfP z.1 z.2)‖)
    (show (u, v) ∈ Set.Icc (-1, -1) (0, 1) from ⟨⟨hu.1, hv.1⟩, ⟨hu.2, hv.2⟩⟩))
  exact le_trans hh (le_abs_self C)

noncomputable def boundaryF (u y : ℝ) : ℝ :=
  -certA u (Real.cos y) * Real.sqrt (1 - u ^ 2) / Real.sqrt (surfP u (Real.cos y))
noncomputable def mainVal (u : ℝ) : ℝ :=
  kernelK u * Real.pi / Real.sqrt 338 * Real.sqrt ((1 - u) / 8)

lemma boundary_point_error (C u v : ℝ) (hu : u ∈ Set.Ioc (-1) 0) (hv : v ∈ Set.Icc (-1) 1)
    (hC : |regularA u v / Real.sqrt (surfP u v)| ≤ C) :
    |-certA u v * Real.sqrt (1 - u ^ 2) / Real.sqrt (surfP u v) -
        (kernelK u / Real.sqrt 338 * Real.sqrt (1 - u ^ 2)) * (1 / kernelD u v)| ≤
      Real.sqrt (1 - u ^ 2) * (C + 64 * |kernelK u|) := by
  have hd := kernelD_pos u v hu hv
  have hs : 0 ≤ Real.sqrt (1 - u ^ 2) := Real.sqrt_nonneg _
  have he := sqrt_kernel_error u v ⟨hu.1.le, hu.2⟩ hv
  rw [certA_split u v hu hv]
  calc
    _ = |-Real.sqrt (1 - u ^ 2) * (regularA u v / Real.sqrt (surfP u v)) +
        (Real.sqrt (1 - u ^ 2) * kernelK u / kernelD u v) *
          (1 / Real.sqrt (surfP u v) - 1 / Real.sqrt 338)| := by congr 1; ring
    _ ≤ |-Real.sqrt (1 - u ^ 2) * (regularA u v / Real.sqrt (surfP u v))| +
        |(Real.sqrt (1 - u ^ 2) * kernelK u / kernelD u v) *
          (1 / Real.sqrt (surfP u v) - 1 / Real.sqrt 338)| := abs_add_le _ _
    _ = Real.sqrt (1 - u ^ 2) * |regularA u v / Real.sqrt (surfP u v)| +
        (Real.sqrt (1 - u ^ 2) * |kernelK u| / kernelD u v) *
          |1 / Real.sqrt (surfP u v) - 1 / Real.sqrt 338| := by
      simp only [abs_mul, abs_neg, abs_div, abs_of_nonneg hs, abs_of_pos hd]
    _ ≤ Real.sqrt (1 - u ^ 2) * C +
        (Real.sqrt (1 - u ^ 2) * |kernelK u| / kernelD u v) * (64 * kernelD u v) := by
      gcongr
    _ = _ := by field_simp

lemma boundaryF_continuous (u : ℝ) (hu : u ∈ Set.Ioc (-1) 0) : Continuous (boundaryF u) := by
  have hA : Continuous (fun y => certA u (Real.cos y)) := by
    unfold certA
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro y
    exact rDen_ne _ _ ⟨hu.1, by linarith [hu.2]⟩ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  unfold boundaryF
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro y
  have hp := (surfP_bounds u (Real.cos y) ⟨hu.1.le, by linarith [hu.2]⟩
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).1
  positivity

lemma kernel_cos_continuous (u : ℝ) (hu : u ∈ Set.Ioc (-1) 0) :
    Continuous (fun y => 1 / kernelD u (Real.cos y)) := by
  apply Continuous.div continuous_const
  · unfold kernelD; fun_prop
  · intro y
    exact (kernelD_pos _ _ hu ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩).ne'

lemma boundary_integral_error (C u : ℝ) (hu : u ∈ Set.Ioc (-1) 0)
    (hC : ∀ v, v ∈ Set.Icc (-1) 1 → |regularA u v / Real.sqrt (surfP u v)| ≤ C) :
    ‖(∫ y in 0..Real.pi, boundaryF u y) - mainVal u‖ ≤
      Real.sqrt (1 - u ^ 2) * (C + 64 * |kernelK u|) * Real.pi := by
  let c : ℝ := kernelK u / Real.sqrt 338 * Real.sqrt (1 - u ^ 2)
  have hm : (∫ y in 0..Real.pi, c * (1 / kernelD u (Real.cos y))) = mainVal u := by
    rw [integral_const_mul]
    dsimp [c, mainVal]
    calc
      _ = (kernelK u / Real.sqrt 338) *
          (Real.sqrt (1 - u ^ 2) * ∫ y in 0..Real.pi, 1 / kernelD u (Real.cos y)) := by ring
      _ = _ := by rw [kernel_mass u hu]; ring
  rw [← hm, ← integral_sub (boundaryF_continuous u hu |>.intervalIntegrable _ _)
    ((continuous_const.mul (kernel_cos_continuous u hu)).intervalIntegrable _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := Real.pi)
    (fun y hy => show ‖boundaryF u y - c * (1 / kernelD u (Real.cos y))‖ ≤
      Real.sqrt (1 - u ^ 2) * (C + 64 * |kernelK u|) from
        boundary_point_error C u (Real.cos y) hu ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
          (hC _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
  simpa [abs_of_nonneg Real.pi_pos.le] using hb

noncomputable def edge (n : ℕ) : ℝ := -1 + 1 / ((n : ℝ) + 1)

lemma edge_mem (n : ℕ) : edge n ∈ Set.Ioc (-1) 0 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hl : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  constructor <;> unfold edge <;> linarith

lemma edge_tendsto : Tendsto edge atTop (𝓝 (-1 : ℝ)) := by
  have h := (tendsto_const_nhds (x := (-1 : ℝ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [add_zero] using h

lemma kernelK_edge_tendsto : Tendsto (fun n => kernelK (edge n)) atTop (𝓝 (10010 : ℝ)) := by
  have hc : ContinuousAt kernelK (-1) := by unfold kernelK; fun_prop (disch := norm_num)
  convert hc.tendsto.comp edge_tendsto using 1
  norm_num [kernelK]

lemma mainVal_edge_tendsto : Tendsto (fun n => mainVal (edge n)) atTop (𝓝 (5005 * Real.pi / Real.sqrt 338)) := by
  have hc : ContinuousAt mainVal (-1) := by unfold mainVal kernelK; fun_prop (disch := norm_num)
  convert hc.tendsto.comp edge_tendsto using 1
  norm_num [mainVal, kernelK]
  ring

lemma boundary_limit : Tendsto (fun n => ∫ y in 0..Real.pi, boundaryF (edge n) y)
    atTop (𝓝 (5005 * Real.pi / Real.sqrt 338)) := by
  obtain ⟨C, hC0, hC⟩ := regularA_uniform_bound
  have hs : Tendsto (fun n => Real.sqrt (1 - edge n ^ 2)) atTop (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun u : ℝ => Real.sqrt (1 - u ^ 2)) := by fun_prop
    simpa using hc.continuousAt.tendsto.comp edge_tendsto
  have hb : Tendsto (fun n => Real.sqrt (1 - edge n ^ 2) * (C + 64 * |kernelK (edge n)|) * Real.pi)
      atTop (𝓝 (0 : ℝ)) := by
    have h := (hs.mul ((tendsto_const_nhds (x := C)).add
      ((tendsto_const_nhds (x := (64 : ℝ))).mul kernelK_edge_tendsto.abs))).mul (tendsto_const_nhds (x := Real.pi))
    simpa using h
  have he : Tendsto (fun n => (∫ y in 0..Real.pi, boundaryF (edge n) y) - mainVal (edge n))
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm _ hb
    intro n
    exact boundary_integral_error C (edge n) (edge_mem n)
      (fun v hv => hC _ _ ⟨(edge_mem n).1.le, (edge_mem n).2⟩ hv)
  convert he.add mainVal_edge_tendsto using 1
  · ext n; ring
  · simp

lemma integral_value : (∫ x in 0..Real.pi, ∫ y in 0..Real.pi, surfI x y) =
    5005 * Real.pi / Real.sqrt 338 := by
  have hc : Continuous (fun x => ∫ y in 0..Real.pi, surfI x y) :=
    continuous_parametric_intervalIntegral_of_continuous' surfI_continuous 0 Real.pi
  have hp : Continuous (fun a => ∫ x in 0..a, ∫ y in 0..Real.pi, surfI x y) :=
    continuous_primitive (fun a b => hc.intervalIntegrable a b) 0
  have ha : Tendsto (fun n => Real.arccos (edge n)) atTop (𝓝 Real.pi) := by
    simpa using Real.continuous_arccos.continuousAt.tendsto.comp edge_tendsto
  have hleft := hp.continuousAt.tendsto.comp ha
  have he (n : ℕ) :
      (∫ x in 0..Real.arccos (edge n), ∫ y in 0..Real.pi, surfI x y) =
        ∫ y in 0..Real.pi, boundaryF (edge n) y := by
    have hu := edge_mem n
    have halt : Real.arccos (edge n) < Real.pi := by
      have h := Real.arccos_lt_arccos (x := (-1 : ℝ)) (by norm_num) hu.1 (by linarith [hu.2])
      simpa using h
    rw [divergence_integral_cut _ (Real.arccos_nonneg _) halt]
    apply integral_congr
    intro y hy
    unfold fluxU boundaryF
    rw [Real.cos_arccos hu.1.le (by linarith [hu.2]), Real.sin_arccos]
  exact tendsto_nhds_unique hleft (boundary_limit.congr' (Filter.Eventually.of_forall fun n => (he n).symm))

lemma result : (∑' n : ℕ, t n) = 5390 / Real.pi := by
  rw [series_as_integral, integral_value]
  have h392 : Real.sqrt (392 : ℝ) ^ 2 = 392 := by norm_num
  have h338 : Real.sqrt (338 : ℝ) ^ 2 = 338 := by norm_num
  have h : Real.sqrt 392 * 5005 = 5390 * Real.sqrt 338 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    nlinarith [h392, h338]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt (338 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [h]

end SunProof


/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.
-/
theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  exact SunProof.result

theorem oeis_a336981_conjecture_2_i.disproof : ¬ (type_of% @oeis_a336981_conjecture_2_i) := sorry
