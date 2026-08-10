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

namespace A336981proof

open Real Polynomial MeasureTheory intervalIntegral Filter

/-! ### Part 1: combinatorial identity -/

lemma choose_id (k i : ℕ) :
    k.choose (2*i) * (2*i).choose i = k.choose i * (k-i).choose i := by
  have h := Nat.choose_mul (n := k) (k := 2*i) (s := i) (by omega)
  simpa [show 2*i - i = i by omega] using h

/-! ### Part 2: Wallis-type integrals -/

lemma prod_ratio (n : ℕ) :
    ∏ i ∈ range n, (2*(i:ℝ)+1)/(2*(i:ℝ)+2) = ((2*n).choose n : ℝ) / 4^n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hc : ((m:ℝ)+1) * ((2*(m+1)).choose (m+1) : ℝ)
        = 2*(2*(m:ℝ)+1) * ((2*m).choose m : ℝ) := by
      have h2 := Nat.succ_mul_centralBinom_succ m
      simp only [Nat.centralBinom] at h2
      exact_mod_cast h2
    have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
    have hC : ((2*(m+1)).choose (m+1) : ℝ)
        = 2*(2*(m:ℝ)+1) * ((2*m).choose m : ℝ) / ((m:ℝ)+1) := by
      field_simp
      linarith [hc]
    rw [Finset.prod_range_succ, ih, hC]
    have h2 : (2*(m:ℝ)+2) ≠ 0 := by positivity
    have h4 : (4:ℝ)^m ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma cos_pow_eq_sin_pow (n : ℕ) :
    ∫ x in (0:ℝ)..π, cos x ^ (2*n) = ∫ x in (0:ℝ)..π, sin x ^ (2*n) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => sin x ^ (2*n)) volume a b :=
    fun a b => (Real.continuous_sin.pow _).intervalIntegrable a b
  have h1 : ∫ x in (0:ℝ)..π, cos x ^ (2*n)
      = ∫ x in (0:ℝ)..π, sin (x + π/2) ^ (2*n) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [Real.sin_add_pi_div_two]
  rw [h1, intervalIntegral.integral_comp_add_right (fun x => sin x ^ (2*n)) (π/2)]
  have h2 : ∫ x in (π:ℝ)..(π + π/2), sin x ^ (2*n) = ∫ x in (0:ℝ)..(π/2), sin x ^ (2*n) := by
    have h3 := intervalIntegral.integral_comp_add_right (a := 0) (b := π/2)
      (fun x => sin x ^ (2*n)) π
    have h4 : ∀ x : ℝ, sin (x + π) ^ (2*n) = sin x ^ (2*n) := by
      intro x
      rw [Real.sin_add_pi, Even.neg_pow (even_two_mul n)]
    rw [intervalIntegral.integral_congr (g := fun x => sin x ^ (2*n)) (fun x _ => h4 x)] at h3
    rw [show (0:ℝ)+π = π from by ring, show π/2+π = π+π/2 from by ring] at h3
    exact h3.symm
  have h5 : (0:ℝ) + π/2 = π/2 := by ring
  rw [h5]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (π/2) π) (hi π (π + π/2)), h2]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (π/2)) (hi (π/2) π)]
  ring

lemma integral_cos_pow_even_pi (n : ℕ) :
    ∫ x in (0:ℝ)..π, cos x ^ (2*n) = π * (((2*n).choose n : ℝ) / 4^n) := by
  rw [cos_pow_eq_sin_pow, integral_sin_pow_even, ← prod_ratio]

lemma integral_cos_pow_odd_pi (n : ℕ) :
    ∫ x in (0:ℝ)..π, cos x ^ (2*n+1) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π)
    (fun x => cos x ^ (2*n+1)) π
  simp only [sub_self, sub_zero] at h
  have h2 : ∀ x : ℝ, cos (π - x) ^ (2*n+1) = -(cos x ^ (2*n+1)) := by
    intro x
    rw [Real.cos_pi_sub, Odd.neg_pow ⟨n, by ring⟩]
  rw [intervalIntegral.integral_congr (g := fun x => -(cos x ^ (2*n+1)))
    (fun x _ => h2 x), intervalIntegral.integral_neg] at h
  linarith

/-! ### Part 3: Ring.choose values at -1/2 and -3/2 -/

lemma ring_choose_succ (a : ℝ) (k : ℕ) :
    Ring.choose a (k+1) = Ring.choose a k * (a - k) / ((k:ℝ)+1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right]
  simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul, pow_one, pow_zero, nsmul_eq_mul, mul_one,
    Nat.factorial_succ, Nat.cast_mul]
  have h1 : ((k:ℝ)+1) ≠ 0 := by positivity
  have h2 : ((k.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  push_cast
  field_simp

lemma cb_recur (m : ℕ) : ((2*(m+1)).choose (m+1) : ℝ)
    = 2*(2*(m:ℝ)+1) * ((2*m).choose m : ℝ) / ((m:ℝ)+1) := by
  have hc : ((m:ℝ)+1) * ((2*(m+1)).choose (m+1) : ℝ)
      = 2*(2*(m:ℝ)+1) * ((2*m).choose m : ℝ) := by
    have h2 := Nat.succ_mul_centralBinom_succ m
    simp only [Nat.centralBinom] at h2
    exact_mod_cast h2
  have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
  field_simp
  linarith [hc]

lemma rc_half (k : ℕ) :
    Ring.choose (-(1/2) : ℝ) k = (-1/4)^k * ((2*k).choose k : ℝ) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [ring_choose_succ, ih, cb_recur]
    have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma rc_3half (k : ℕ) :
    Ring.choose (-(3/2) : ℝ) k = (-1/4)^k * (2*(k:ℝ)+1) * ((2*k).choose k : ℝ) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [ring_choose_succ, ih, cb_recur]
    have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-! ### Part 4: integral representation of T_k -/

lemma T_int (k : ℕ) (b d : ℝ) :
    ∫ x in (0:ℝ)..π, (b + 2*d*cos x)^k
      = π * ∑ i ∈ range (k/2+1),
          ((k.choose i * (k-i).choose i : ℕ) : ℝ) * (b^(k-2*i) * (d^2)^i) := by
  have hexp : ∀ x : ℝ, (b + 2*d*cos x)^k
      = ∑ j ∈ range (k+1), b^(k-j) * (2*d)^j * (k.choose j : ℝ) * cos x ^ j := by
    intro x
    rw [add_comm b, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
    ring
  simp only [hexp]
  rw [intervalIntegral.integral_finset_sum (fun j _ =>
    ((continuous_const.mul (Real.continuous_cos.pow j)).intervalIntegrable 0 π))]
  simp only [intervalIntegral.integral_const_mul]
  rw [← Finset.sum_filter_of_ne (p := fun j => Even j) (f := fun j =>
      b^(k-j) * (2*d)^j * (k.choose j : ℝ) * ∫ x in (0:ℝ)..π, cos x ^ j)
    (by
      intro j hj hne
      by_contra hodd
      obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hodd
      apply hne
      subst hm
      simp only [integral_cos_pow_odd_pi, mul_zero])]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun j => j/2) (j := fun i => 2*i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have := hj.2
    rw [Nat.even_iff] at this
    simp only [Finset.mem_range]
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact even_two_mul i
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have := hj.2
    rw [Nat.even_iff] at this
    beta_reduce
    omega
  · intro i hi
    beta_reduce
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjk, hje⟩ := hj
    obtain ⟨m, hm⟩ := hje
    have hj2 : j = 2*m := by omega
    subst hj2
    beta_reduce
    simp only [Nat.mul_div_cancel_left m (by norm_num : (0:ℕ) < 2)]
    rw [integral_cos_pow_even_pi m]
    have hpow : (2*d)^(2*m) = 4^m * (d^2)^m := by
      rw [pow_mul, show (2*d)^2 = 4*d^2 from by ring, mul_pow]
    rw [hpow]
    have h4 : ((4:ℝ)^m) ≠ 0 := by positivity
    have hcc : ((k.choose (2*m) : ℝ)) * ((2*m).choose m : ℝ)
        = (k.choose m : ℝ) * ((k-m).choose m : ℝ) := by
      exact_mod_cast choose_id k m
    push_cast
    field_simp
    linear_combination (b^(k-2*m) * (d^2)^m) * hcc

lemma T1_rep (k : ℕ) :
    ∫ x in (0:ℝ)..π, (14 + 2*cos x)^k = π * ((T_k k 14 1 : ℚ) : ℝ) := by
  have h := T_int k 14 1
  simp only [mul_one] at h
  rw [h, T_k]
  push_cast
  norm_num

lemma T2_rep (k : ℕ) :
    ∫ x in (0:ℝ)..π, (17 + 8*cos x)^k = π * ((T_k k 17 16 : ℚ) : ℝ) := by
  have h := T_int k 17 4
  norm_num at h
  rw [h, T_k]
  push_cast
  norm_num

/-! ### Part 5: t k as a double integral -/

lemma t_eq_double (k : ℕ) :
    t k = (1/π^2) * ∫ θ in (0:ℝ)..π, ∫ ph in (0:ℝ)..π,
      (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ)
        * (((14+2*cos θ)*(17+8*cos ph))/3136)^k := by
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  have hin : ∀ θ : ℝ, (∫ ph in (0:ℝ)..π,
      (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k)
      = ((367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * ((14+2*cos θ)^k/3136^k))
        * ∫ ph in (0:ℝ)..π, (17+8*cos ph)^k := by
    intro θ
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ph _ => ?_
    rw [div_pow, mul_pow]
    ring
  simp only [hin]
  have hout : (∫ θ in (0:ℝ)..π, ((367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ)
        * ((14+2*cos θ)^k/3136^k)) * ∫ ph in (0:ℝ)..π, (17+8*cos ph)^k)
      = ((367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) / 3136^k
          * ∫ ph in (0:ℝ)..π, (17+8*cos ph)^k) * ∫ θ in (0:ℝ)..π, (14+2*cos θ)^k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [hout, T1_rep, T2_rep]
  simp only [t]
  field_simp
  ring

/-! ### Part 6: binomial series -/

lemma binomial_hasSum (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => Ring.choose a k * x^k) ((1+x)^a) := by
  have h := _root_.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)
  have hx' : x ∈ EMetric.ball (0:ℝ) 1 := by
    rw [EMetric.mem_ball, edist_dist, _root_.dist_zero_right, Real.norm_eq_abs]
    exact_mod_cast ENNReal.ofReal_lt_one.mpr hx
  have h2 := h.hasSum hx'
  simp only [zero_add, binomialSeries_apply, smul_eq_mul, List.ofFn_const,
    List.prod_replicate] at h2
  exact h2

/-! ### Part 7: closed form of the k-sum -/

lemma inner_hasSum {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 784) :
    HasSum (fun k : ℕ => (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (w/3136)^k)
      (392 * (20552 + 127*w) / ((784 - w) * Real.sqrt (784 - w))) := by
  have hx : |(-(w/784) : ℝ)| < 1 := by
    rw [abs_lt]
    constructor
    · nlinarith
    · nlinarith
  have hb1 := binomial_hasSum (-(1/2)) hx
  have hb3 := binomial_hasSum (-(3/2)) hx
  have hq : ((-1:ℝ)/4) * (-(w/784)) = w/3136 := by ring
  have e1 : ∀ k : ℕ, Ring.choose (-(1/2):ℝ) k * (-(w/784))^k
      = ((2*k).choose k : ℝ) * (w/3136)^k := by
    intro k
    rw [rc_half, ← hq, mul_pow]
    ring
  have e3 : ∀ k : ℕ, Ring.choose (-(3/2):ℝ) k * (-(w/784))^k
      = (2*(k:ℝ)+1) * (((2*k).choose k : ℝ) * (w/3136)^k) := by
    intro k
    rw [rc_3half, ← hq, mul_pow]
    ring
  simp only [e1] at hb1
  simp only [e3] at hb3
  have hcomb := (hb3.mul_left 2145).sub (hb1.mul_left 1778)
  have hterm : ∀ k : ℕ, 2145*((2*(k:ℝ)+1) * (((2*k).choose k : ℝ) * (w/3136)^k))
      - 1778*(((2*k).choose k : ℝ) * (w/3136)^k)
      = (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (w/3136)^k := by
    intro k; ring
  simp only [hterm] at hcomb
  convert hcomb using 1
  -- value identity
  have hA : (0:ℝ) < 784 - w := by linarith
  have hrw : (1:ℝ) + -(w/784) = (784-w)/784 := by ring
  have hA784 : (0:ℝ) < (784-w)/784 := by positivity
  have hs0 : (0:ℝ) < Real.sqrt (784-w) := Real.sqrt_pos.mpr hA
  have hs2 : Real.sqrt (784-w)^2 = 784-w := Real.sq_sqrt hA.le
  have hsq : Real.sqrt ((784-w)/784) = Real.sqrt (784-w) / 28 := by
    rw [show ((784-w)/784:ℝ) = (Real.sqrt (784-w) / 28)^2 from by
      rw [div_pow, hs2]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have h1' : ((784-w)/784:ℝ)^(-(1/2):ℝ) = 28/Real.sqrt (784-w) := by
    rw [Real.rpow_neg hA784.le, ← Real.sqrt_eq_rpow, hsq, inv_div]
  have h3' : ((784-w)/784:ℝ)^(-(3/2):ℝ) = (28/Real.sqrt (784-w))^(3:ℕ) := by
    rw [show (-(3/2):ℝ) = (-(1/2)) * ((3:ℕ):ℝ) from by norm_num,
      Real.rpow_mul hA784.le, Real.rpow_natCast, h1']
  have hcube : (28/Real.sqrt (784-w))^(3:ℕ) = 21952/((784-w)*Real.sqrt (784-w)) := by
    rw [div_pow, show (Real.sqrt (784-w))^(3:ℕ) = Real.sqrt (784-w)^2 * Real.sqrt (784-w) from by
      ring, hs2]
    norm_num
  rw [hrw, h1', h3', hcube]
  have hAne : (784-w) ≠ 0 := ne_of_gt hA
  have hsne : Real.sqrt (784-w) ≠ 0 := ne_of_gt hs0
  field_simp
  ring

/-! ### Part 8: bounds -/

lemma GH_pos (θ ph : ℝ) : (0:ℝ) < (14+2*cos θ) * (17+8*cos ph) :=
  mul_pos (by nlinarith [Real.neg_one_le_cos θ]) (by nlinarith [Real.neg_one_le_cos ph])

lemma GH_le (θ ph : ℝ) : (14+2*cos θ) * (17+8*cos ph) ≤ 400 := by
  have h1 : (14+2*cos θ) ≤ 16 := by nlinarith [Real.cos_le_one θ]
  have h2 : (17+8*cos ph) ≤ 25 := by nlinarith [Real.cos_le_one ph]
  have h3 : (0:ℝ) < 17+8*cos ph := by nlinarith [Real.neg_one_le_cos ph]
  have h4 : (0:ℝ) < 14+2*cos θ := by nlinarith [Real.neg_one_le_cos θ]
  nlinarith

lemma M_summable : Summable (fun k : ℕ => (367 + 4290*(k:ℝ)) * (25/49)^k) := by
  have h1 : Summable (fun k : ℕ => (367:ℝ) * (25/49)^k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 367
  have h2 : Summable (fun k : ℕ => (4290:ℝ) * ((k:ℝ)^1 * (25/49)^k)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (25/49:ℝ)) (by rw [Real.norm_eq_abs]; norm_num)).mul_left 4290
  refine (h1.add h2).congr fun k => ?_
  ring

lemma f_le_M (k : ℕ) {v : ℝ} (h0 : 0 ≤ v) (h4 : v ≤ 400) :
    (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (v/3136)^k
      ≤ (367 + 4290*(k:ℝ)) * (25/49)^k := by
  have hc : ((2*k).choose k : ℝ) ≤ 4^k := by
    have h := Nat.choose_le_two_pow (2*k) k
    have h2 : ((2:ℕ)^(2*k) : ℝ) = 4^k := by
      push_cast
      rw [pow_mul]
      norm_num
    calc ((2*k).choose k : ℝ) ≤ ((2:ℕ)^(2*k) : ℝ) := by exact_mod_cast h
    _ = 4^k := h2
  have step : (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (v/3136)^k
      ≤ (367 + 4290*(k:ℝ)) * (4:ℝ)^k * (400/3136)^k := by
    gcongr
  calc (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (v/3136)^k
      ≤ (367 + 4290*(k:ℝ)) * (4:ℝ)^k * (400/3136)^k := step
    _ = (367 + 4290*(k:ℝ)) * (25/49)^k := by
        rw [mul_assoc, ← mul_pow]
        norm_num

lemma f_nonneg (k : ℕ) (θ ph : ℝ) :
    0 ≤ (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ)
      * (((14+2*cos θ)*(17+8*cos ph))/3136)^k := by
  have h := GH_pos θ ph
  have h1 : (0:ℝ) ≤ ((14+2*cos θ)*(17+8*cos ph))/3136 := by positivity
  positivity

/-! ### Part 9: the two swaps -/

lemma inner_factor (k : ℕ) (θ : ℝ) : (∫ ph in (0:ℝ)..π,
    (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k)
    = ((367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * ((14+2*cos θ)^k/3136^k))
      * ∫ ph in (0:ℝ)..π, (17+8*cos ph)^k := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ph _ => ?_
  rw [div_pow, mul_pow]
  ring

lemma inner_swap (θ : ℝ) :
    HasSum (fun k : ℕ => ∫ ph in (0:ℝ)..π,
        (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k)
      (∫ ph in (0:ℝ)..π, 392 * (20552 + 127*((14+2*cos θ)*(17+8*cos ph)))
        / ((784 - (14+2*cos θ)*(17+8*cos ph))
            * Real.sqrt (784 - (14+2*cos θ)*(17+8*cos ph)))) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun (k : ℕ) (_ : ℝ) => (367 + 4290*(k:ℝ)) * (25/49)^k)
  · intro k
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · intro k
    filter_upwards with ph _
    rw [Real.norm_eq_abs, abs_of_nonneg (f_nonneg k θ ph)]
    exact f_le_M k (GH_pos θ ph).le (GH_le θ ph)
  · filter_upwards with ph _
    exact M_summable
  · exact _root_.intervalIntegrable_const
  · filter_upwards with ph _
    exact inner_hasSum (GH_pos θ ph).le (by linarith [GH_le θ ph])

lemma outer_swap :
    HasSum (fun k : ℕ => ∫ θ in (0:ℝ)..π, ∫ ph in (0:ℝ)..π,
        (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k)
      (∫ θ in (0:ℝ)..π, ∫ ph in (0:ℝ)..π, 392 * (20552 + 127*((14+2*cos θ)*(17+8*cos ph)))
        / ((784 - (14+2*cos θ)*(17+8*cos ph))
            * Real.sqrt (784 - (14+2*cos θ)*(17+8*cos ph)))) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun (k : ℕ) (_ : ℝ) => π * ((367 + 4290*(k:ℝ)) * (25/49)^k))
  · intro k
    have hfun : (fun θ => ∫ ph in (0:ℝ)..π,
        (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k)
        = (fun θ => ((367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * ((14+2*cos θ)^k/3136^k))
            * ∫ ph in (0:ℝ)..π, (17+8*cos ph)^k) := funext fun θ => inner_factor k θ
    rw [hfun]
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · intro k
    filter_upwards with θ _
    have hint : IntervalIntegrable (fun ph => (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ)
        * (((14+2*cos θ)*(17+8*cos ph))/3136)^k) volume 0 π :=
      Continuous.intervalIntegrable (by fun_prop) 0 π
    have h0' : 0 ≤ ∫ ph in (0:ℝ)..π,
        (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k :=
      intervalIntegral.integral_nonneg Real.pi_pos.le (fun ph _ => f_nonneg k θ ph)
    rw [Real.norm_eq_abs, abs_of_nonneg h0']
    have hle : (∫ ph in (0:ℝ)..π,
        (367 + 4290*(k:ℝ)) * ((2*k).choose k : ℝ) * (((14+2*cos θ)*(17+8*cos ph))/3136)^k)
        ≤ ∫ _ph in (0:ℝ)..π, (367 + 4290*(k:ℝ)) * (25/49)^k := by
      apply intervalIntegral.integral_mono_on Real.pi_pos.le hint _root_.intervalIntegrable_const
      intro ph _
      exact f_le_M k (GH_pos θ ph).le (GH_le θ ph)
    calc _ ≤ ∫ _ph in (0:ℝ)..π, (367 + 4290*(k:ℝ)) * (25/49)^k := hle
      _ = π * ((367 + 4290*(k:ℝ)) * (25/49)^k) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  · filter_upwards with θ _
    exact M_summable.mul_left π
  · exact _root_.intervalIntegrable_const
  · filter_upwards with θ _
    exact inner_swap θ

/-! ### Part 10: the core double-integral evaluation -/

lemma Jcore : (∫ θ in (0:ℝ)..π, ∫ ph in (0:ℝ)..π,
    392 * (20552 + 127*((14+2*cos θ)*(17+8*cos ph)))
      / ((784 - (14+2*cos θ)*(17+8*cos ph))
          * Real.sqrt (784 - (14+2*cos θ)*(17+8*cos ph)))) = 5390 * π := by
  sorry

end A336981proof

/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.
-/
theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h2 := A336981proof.outer_swap.mul_left (1/Real.pi^2)
  simp only [← A336981proof.t_eq_double] at h2
  rw [h2.tsum_eq, A336981proof.Jcore]
  field_simp
