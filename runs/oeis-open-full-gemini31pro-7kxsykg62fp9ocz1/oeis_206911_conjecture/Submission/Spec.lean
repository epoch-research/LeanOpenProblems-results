import FormalConjectures.Util.ProblemImports

open Real Nat Finset Filter

/--
A206911: Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked with the set $\{\log(k+1)\}$; complement of A206912.
The $n$-th term $a(n)$ is the rank of $S(n) = \sum_{i=1}^n 1/i$ in the sorted list.
This rank is computed as $n + \lfloor \exp(S(n)) - 1 \rfloor$.
-/
noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- Count of log terms is $\lfloor e^{S_n} - 1 \rfloor$
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat

/-- The difference sequence D(n) = A206911(n+1) - A206911(n), indexed starting at n=1. -/
noncomputable def A206911_diff (n : ℕ) : ℕ := A206911 (n + 1) - A206911 n

/-- The number of 3s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_3s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of 2s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_2s (N : ℕ) : ℕ :=
 (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0

lemma harm_nonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  induction' n with n ih
  · simp
  · rw [harmonic_succ]
    push_cast
    positivity

lemma a206911_S_n_eq_harmonic (n : ℕ) : (range n).sum (fun k => 1 / ((k : ℝ) + 1)) = harmonic n := by
  induction' n with n ih
  · simp
  · rw [sum_range_succ, ih, harmonic_succ]
    push_cast
    rw [one_div]

lemma A206911_eq (n : ℕ) : A206911 n = n + ⌊exp (harmonic n) - 1⌋₊ := by
  change n + ⌊rexp _ - 1⌋₊ = _
  rw [a206911_S_n_eq_harmonic]

lemma floor_add_floor_le (a b : ℝ) : Int.floor a + Int.floor b ≤ Int.floor (a + b) := by
  rw [Int.le_floor]
  push_cast
  exact add_le_add (Int.floor_le a) (Int.floor_le b)

lemma floor_add_le_floor_add_floor_add_one (a b : ℝ) : Int.floor (a + b) ≤ Int.floor a + Int.floor b + 1 := by
  rw [Int.floor_le_iff]
  push_cast
  have h1 := Int.lt_floor_add_one a
  have h2 := Int.lt_floor_add_one b
  linarith

lemma floor_sub_floor (x y : ℝ) : Int.floor x - Int.floor y = Int.floor (x - y) ∨ Int.floor x - Int.floor y = Int.floor (x - y) + 1 := by
  have h1 := floor_add_floor_le y (x - y)
  have h2 := floor_add_le_floor_add_floor_add_one y (x - y)
  have : y + (x - y) = x := add_sub_cancel y x
  rw [this] at h1 h2
  omega

lemma diff_eq_2_or_3 {x y : ℝ} (h_pos_y : 0 ≤ y) (h_pos_x : 0 ≤ x) (h_bound : 1 < x - y ∧ x - y < 2) :
    let diff := 1 + (Int.toNat (Int.floor x)) - (Int.toNat (Int.floor y))
    diff = 2 ∨ diff = 3 := by
  intro diff
  have h_floor : Int.floor (x - y) = 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨h_bound.left.le, by linarith [h_bound.right]⟩
  have h_cases := floor_sub_floor x y
  rw [h_floor] at h_cases
  have h_cast_y : (Int.toNat (Int.floor y) : ℤ) = Int.floor y := Int.toNat_of_nonneg (Int.floor_nonneg.mpr h_pos_y)
  have h_cast_x : (Int.toNat (Int.floor x) : ℤ) = Int.floor x := Int.toNat_of_nonneg (Int.floor_nonneg.mpr h_pos_x)
  dsimp [diff]
  omega

lemma bound_add_helper (x y : ℝ) (hy : y * (1 + x) = x) :
    let A_minus_1 := y + y^2/2 + y^3/6 + y^4/24
    let B := 1 + x + x^2/2 + x^3/6 + 5/96 * x^4
    (A_minus_1 * B + 1 - B) * (2304 * (1+x)^4) = 85*x^8 + 292*x^7 + 580*x^6 + 504*x^5 + 168*x^4 := by
  intro A_minus_1 B
  have hy2 : y^2 * (1+x)^2 = x^2 := by
    calc y^2 * (1+x)^2 = (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x := by rw [hy]
    _ = x^2 := by ring
  have hy3 : y^3 * (1+x)^3 = x^3 := by
    calc y^3 * (1+x)^3 = (y * (1+x)) * (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x * x := by rw [hy]
    _ = x^3 := by ring
  have hy4 : y^4 * (1+x)^4 = x^4 := by
    calc y^4 * (1+x)^4 = (y * (1+x)) * (y * (1+x)) * (y * (1+x)) * (y * (1+x)) := by ring
    _ = x * x * x * x := by rw [hy]
    _ = x^4 := by ring
  have h_A : A_minus_1 * 24 * (1+x)^4 = 24 * x * (1+x)^3 + 12 * x^2 * (1+x)^2 + 4 * x^3 * (1+x) + x^4 := by
    calc
      A_minus_1 * 24 * (1+x)^4 = 24 * (y * (1+x) * (1+x)^3) + 12 * (y^2 * (1+x)^2 * (1+x)^2) + 4 * (y^3 * (1+x)^3 * (1+x)) + (y^4 * (1+x)^4) := by
        dsimp [A_minus_1]
        ring
      _ = 24 * (x * (1+x)^3) + 12 * (x^2 * (1+x)^2) + 4 * (x^3 * (1+x)) + x^4 := by rw [hy, hy2, hy3, hy4]
      _ = 24 * x * (1+x)^3 + 12 * x^2 * (1+x)^2 + 4 * x^3 * (1+x) + x^4 := by ring
  have h_full : (A_minus_1 * B + 1 - B) * (2304 * (1+x)^4) = (A_minus_1 * 24 * (1+x)^4) * (96 * B) + 2304 * (1+x)^4 * (1 - B) := by ring
  rw [h_full, h_A]
  dsimp [B]
  ring

lemma exp_lower_bound (x : ℝ) (hx : 0 ≤ x) :
    1 + x/(1+x) + (x/(1+x))^2/2 + (x/(1+x))^3/6 + (x/(1+x))^4/24 ≤ exp (x / (1 + x)) := by
  have H := sum_le_exp_of_nonneg (x := x / (1 + x)) (by positivity) 5
  have h_eq : ∑ i ∈ range 5, (x / (1 + x)) ^ i / (Nat.factorial i : ℝ) = 1 + x/(1+x) + (x/(1+x))^2/2 + (x/(1+x))^3/6 + (x/(1+x))^4/24 := by
    simp [sum_range_succ]
    ring
  rwa [h_eq] at H

lemma exp_upper_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp x ≤ 1 + x + x^2/2 + x^3/6 + 5/96 * x^4 := by
  have H := exp_bound (x := x) (by exact (abs_le.mpr ⟨by linarith, hx1⟩)) (n := 4) (by decide)
  have h_eq : ∑ m ∈ range 4, x ^ m / (Nat.factorial m : ℝ) = 1 + x + x^2/2 + x^3/6 := by
    simp [sum_range_succ]
    ring
  rw [h_eq] at H
  have : (4 : ℕ).succ = 5 := rfl
  rw [this] at H
  have : ((4 : ℕ).factorial : ℝ) = 24 := rfl
  rw [this] at H
  have h_abs : |x| = x := abs_of_nonneg hx0
  rw [h_abs] at H
  have H_le := (le_abs_self _).trans H
  linarith

lemma exp_neg_lower_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x + x^2/2 + x^3/6 + 5/96 * x^4)⁻¹ ≤ exp (-x) := by
  have := exp_upper_bound x hx0 hx1
  have hB_pos : 0 < 1 + x + x^2/2 + x^3/6 + 5/96 * x^4 := by
    have hexp := exp_pos x
    linarith
  rw [exp_neg]
  exact (inv_le_inv₀ hB_pos (exp_pos x)).mpr this

lemma bound_add (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1/2) :
    2 < exp (x / (1 + x)) + exp (-x) := by
  let A := 1 + x/(1+x) + (x/(1+x))^2/2 + (x/(1+x))^3/6 + (x/(1+x))^4/24
  let B := 1 + x + x^2/2 + x^3/6 + 5/96 * x^4
  have H1 : A ≤ exp (x / (1 + x)) := exp_lower_bound x hx0.le
  have H2 : B⁻¹ ≤ exp (-x) := exp_neg_lower_bound x hx0.le (by linarith)
  have H_le : A + B⁻¹ ≤ exp (x / (1 + x)) + exp (-x) := add_le_add H1 H2
  have h_pos : 0 < B := by
    dsimp [B]; positivity
  have h_alg : ((A - 1) * B + 1 - B) * (2304 * (1+x)^4) = 85*x^8 + 292*x^7 + 580*x^6 + 504*x^5 + 168*x^4 := by
    have hy : (x / (1+x)) * (1+x) = x := div_mul_cancel₀ x (by positivity)
    have H_helper := bound_add_helper x (x / (1+x)) hy
    dsimp at H_helper
    have h_eq : A - 1 = x / (1 + x) + (x / (1 + x)) ^ 2 / 2 + (x / (1 + x)) ^ 3 / 6 + (x / (1 + x)) ^ 4 / 24 := by
      dsimp [A]
      ring
    rw [h_eq]
    exact H_helper
  have h_alg_pos : 0 < ((A - 1) * B + 1 - B) * (2304 * (1+x)^4) := by
    rw [h_alg]
    positivity
  have h_pos2 : 0 < 2304 * (1+x)^4 := by positivity
  have h_A_B : 0 < (A - 1) * B + 1 - B := pos_of_mul_pos_left h_alg_pos h_pos2.le
  have h_A_B2 : B - 1 < (A - 1) * B := by linarith
  have h_A_B3 : (B - 1) / B < A - 1 := by
    rwa [div_lt_iff₀ h_pos]
  have H_gt : 2 < A + B⁻¹ := by
    have : (B - 1) / B = 1 - B⁻¹ := by
      rw [sub_div, div_self h_pos.ne.symm, one_div]
    rw [this] at h_A_B3
    linarith
  exact H_gt.trans_le H_le

lemma c_ratio (x : ℝ) (h_bound : 2 < exp (x / (1 + x)) + exp (-x)) :
    exp x - 1 < exp x * (exp (x / (1 + x)) - 1) := by
  have H1 : exp x * (2 - exp (-x)) < exp x * exp (x / (1 + x)) := by
    apply mul_lt_mul_of_pos_left
    · linarith
    · exact exp_pos x
  have h_eq : exp x * (2 - exp (-x)) = 2 * exp x - 1 := by
    rw [mul_sub, ← exp_add]
    have : x + -x = 0 := add_neg_cancel x
    rw [this, exp_zero]
    ring
  rw [h_eq] at H1
  linarith

lemma c_mono (n : ℕ) (hn : 1 ≤ n) : exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) < exp (harmonic (n + 1)) * (exp (1 / (n + 2 : ℝ)) - 1) := by
  have H := c_ratio (1 / (n + 1 : ℝ)) (bound_add (1 / (n + 1 : ℝ)) (by positivity) (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (2 : ℝ) ≤ n + 1 := by linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  ))
  have h_eq : (1 / (n + 1 : ℝ)) / (1 + 1 / (n + 1 : ℝ)) = 1 / (n + 2 : ℝ) := by
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    have hn3 : 1 + 1 / (n + 1 : ℝ) ≠ 0 := by positivity
    apply mul_right_cancel₀ hn3
    rw [div_mul_cancel₀ _ hn3]
    apply mul_left_cancel₀ hn2
    rw [← mul_assoc, mul_div_cancel₀ 1 hn2, one_mul]
    have : (n + 2 : ℝ) = (n + 1 : ℝ) + 1 := by ring
    rw [this, add_mul, mul_one_div_cancel hn1]
    ring
  rw [h_eq] at H
  have h_harm : (harmonic (n + 1) : ℝ) = harmonic n + 1 / (n + 1 : ℝ) := by
    rw [harmonic_succ]; push_cast; rw [one_div]
  rw [h_harm, exp_add]
  calc
    exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) - 1) < exp (harmonic n) * (exp (1 / (n + 1 : ℝ)) * (exp (1 / (n + 2 : ℝ)) - 1)) := by
      apply mul_lt_mul_of_pos_left H (exp_pos _)
    _ = exp (harmonic n) * exp (1 / (n + 1 : ℝ)) * (exp (1 / (n + 2 : ℝ)) - 1) := by ring

lemma c_mono_le {c : ℕ → ℝ} (h : ∀ n, 1 ≤ n → c n ≤ c (n + 1)) (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) : c n ≤ c m := by
  induction' m, hnm using Nat.le_induction with k hk ih
  · rfl
  · have h_k : c k ≤ c (k + 1) := h k (hn.trans hk)
    exact ih.trans h_k

lemma c_upper_bound (n : ℕ) : exp (harmonic (n + 1)) - exp (harmonic n) < exp (harmonic (n + 1)) / (n + 1 : ℝ) := by
  have h1 : (harmonic n : ℝ) = harmonic (n + 1) - 1 / (n + 1 : ℝ) := by
    rw [harmonic_succ]
    push_cast
    ring
  have h2 : exp (harmonic n) = exp (harmonic (n + 1)) * exp (- (1 / (n + 1 : ℝ))) := by
    calc
      exp (harmonic n) = exp (harmonic (n + 1) - 1 / (n + 1 : ℝ)) := by rw [h1]
      _ = exp (harmonic (n + 1) + - (1 / (n + 1 : ℝ))) := by ring_nf
      _ = exp (harmonic (n + 1)) * exp (- (1 / (n + 1 : ℝ))) := by rw [exp_add]
  rw [h2]
  have h3 : -(1 / (n + 1 : ℝ)) + 1 < exp (- (1 / (n + 1 : ℝ))) := by
    apply add_one_lt_exp
    have : (n + 1 : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr (one_div_ne_zero this)
  have h4 : 1 - exp (- (1 / (n + 1 : ℝ))) < 1 / (n + 1 : ℝ) := by linarith
  calc
    exp (harmonic (n + 1)) - exp (harmonic (n + 1)) * exp (- (1 / (n + 1 : ℝ))) = exp (harmonic (n + 1)) * (1 - exp (- (1 / (n + 1 : ℝ)))) := by ring
    _ < exp (harmonic (n + 1)) * (1 / (n + 1 : ℝ)) := by
      apply mul_lt_mul_of_pos_left h4 (exp_pos _)
    _ = exp (harmonic (n + 1)) / (n + 1 : ℝ) := by ring

lemma exp_upper_bound_7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    exp x ≤ 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + 1/4410 * x^7 := by
  have H := exp_bound (x := x) (by exact (abs_le.mpr ⟨by linarith, hx1⟩)) (n := 7) (by decide)
  have h_eq : ∑ m ∈ range 7, x ^ m / (Nat.factorial m : ℝ) = 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 := by
    simp [sum_range_succ]
    ring
  rw [h_eq] at H
  have : (7 : ℕ).succ = 8 := rfl
  rw [this] at H
  have : ((7 : ℕ).factorial : ℝ) = 5040 := rfl
  rw [this] at H
  have h_abs : |x| = x := abs_of_nonneg hx0
  rw [h_abs] at H
  have H_le := (le_abs_self _).trans H
  have h_c : ((8 : ℕ) : ℝ) / (5040 * ((7 : ℕ) : ℝ)) = 1 / 4410 := by norm_num
  rw [h_c] at H_le
  linarith

lemma exp_harmonic_div_n_anti (n : ℕ) (hn : 1 ≤ n) : exp (harmonic (n + 1)) / (n + 1 : ℝ) < exp (harmonic n) / (n : ℝ) := by
  have h1 : (harmonic (n + 1) : ℝ) = harmonic n + 1 / (n + 1 : ℝ) := by
    rw [harmonic_succ]
    push_cast
    rw [one_div]
  rw [h1, exp_add]
  let x := 1 / (n + 1 : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    have : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_add_left 1 n
    exact one_div_le_one_div_of_le (by norm_num) this |>.trans_eq (by norm_num)
  have h2 := exp_upper_bound_7 x hx0 hx1
  have h3 : 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + 1/4410 * x^7 < (n + 1 : ℝ) / (n : ℝ) := by
    have h_alg : 1 - (1 - x) * (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + 1/4410 * x^7) = x^8/4410 + 41*x^7/35280 + x^6/144 + x^5/30 + x^4/8 + x^3/3 + x^2/2 := by ring
    have h_pos : 0 < 1 - (1 - x) * (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + 1/4410 * x^7) := by
      rw [h_alg]
      have : 0 < x := by positivity
      positivity
    have h_1_x : 1 - x = (n : ℝ) / (n + 1 : ℝ) := by
      dsimp [x]
      have : (n + 1 : ℝ) ≠ 0 := by positivity
      apply mul_right_cancel₀ this
      rw [sub_mul, one_mul, div_mul_cancel₀ _ this, div_mul_cancel₀ _ this]
      ring
    have h_1_x_pos : 0 < 1 - x := by
      rw [h_1_x]
      positivity
    have h4 : (1 - x) * (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + 1/4410 * x^7) < 1 := by linarith
    have h5 : 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + 1/4410 * x^7 < 1 / (1 - x) := by
      rwa [lt_div_iff₀ h_1_x_pos, mul_comm]
    have h6 : 1 / (1 - x) = (n + 1 : ℝ) / (n : ℝ) := by
      rw [h_1_x]
      have hn_pos : (n : ℝ) ≠ 0 := by positivity
      have hn1_pos : (n + 1 : ℝ) ≠ 0 := by positivity
      exact one_div_div (n : ℝ) (n + 1 : ℝ)
    rwa [h6] at h5
  have h4 : exp x < (n + 1 : ℝ) / (n : ℝ) := h2.trans_lt h3
  calc
    exp (harmonic n) * exp x / (n + 1 : ℝ) < exp (harmonic n) * ((n + 1 : ℝ) / (n : ℝ)) / (n + 1 : ℝ) := by
      apply div_lt_div_of_pos_right
      · apply mul_lt_mul_of_pos_left h4 (exp_pos _)
      · positivity
    _ = exp (harmonic n) / (n : ℝ) := by
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      have hn2 : (n : ℝ) ≠ 0 := by positivity
      calc exp (harmonic n) * ((n + 1 : ℝ) / (n : ℝ)) / (n + 1 : ℝ) = exp (harmonic n) * ((n + 1 : ℝ) / (n : ℝ) * (1 / (n + 1 : ℝ))) := by ring
      _ = exp (harmonic n) * (1 / (n : ℝ)) := by
        congr 1
        calc ((n + 1 : ℝ) / (n : ℝ)) * (1 / (n + 1 : ℝ)) = ((n + 1 : ℝ) * 1) / ((n : ℝ) * (n + 1 : ℝ)) := div_mul_div_comm _ _ _ _
        _ = (n + 1 : ℝ) / ((n + 1 : ℝ) * (n : ℝ)) := by ring
        _ = 1 / (n : ℝ) := by rw [div_mul_eq_div_div, div_self hn1, one_div]
      _ = exp (harmonic n) / (n : ℝ) := by ring

lemma exp_harmonic_div_n_le_600 (n : ℕ) (hn : 600 ≤ n) : exp (harmonic n) / (n : ℝ) ≤ exp (harmonic 600) / 600 := by
  induction' n, hn using Nat.le_induction with k hk ih
  · rfl
  · have h_anti := exp_harmonic_div_n_anti k (by omega)
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
    have h_cast : exp (harmonic (k + 1)) / ((k + 1 : ℕ) : ℝ) ≤ exp (harmonic k) / (k : ℝ) := by
      rw [hc]
      exact h_anti.le
    exact h_cast.trans ih

set_option maxRecDepth 50000

lemma exp_harmonic_600_upper : exp (harmonic 600) < (41 * 600 : ℝ) / 23 := by
  have h1 : (harmonic 600 : ℝ) < (279 : ℝ) / 40 := by norm_num
  have h2 : exp (harmonic 600) < exp (279 / 40) := exp_lt_exp.mpr h1
  have h3 : (279 : ℝ) / 40 = ((7 : ℕ) : ℝ) * (279 / 280) := by norm_num
  have h4 : exp (279 / 40) = (exp (279 / 280)) ^ 7 := by
    rw [h3, exp_nat_mul]
  have h5 : exp (279 / 280) ≤ 1 + 279/280 + (279/280)^2/2 + (279/280)^3/6 + (279/280)^4/24 + (279/280)^5/120 + (279/280)^6/720 + 1/4410 * (279/280)^7 := by
    exact exp_upper_bound_7 _ (by norm_num) (by norm_num)
  have h6 : (1 + (279:ℝ)/280 + (279/280)^2/2 + (279/280)^3/6 + (279/280)^4/24 + (279/280)^5/120 + (279/280)^6/720 + 1/4410 * (279/280)^7)^7 < (41 * 600 : ℝ) / 23 := by norm_num
  have h7 : (exp (279 / 280)) ^ 7 ≤ (1 + (279:ℝ)/280 + (279/280)^2/2 + (279/280)^3/6 + (279/280)^4/24 + (279/280)^5/120 + (279/280)^6/720 + 1/4410 * (279/280)^7)^7 := by
    apply pow_le_pow_left₀
    · positivity
    · exact h5
  linarith

lemma exp_lower_bound_7 (x : ℝ) (hx : 0 ≤ x) :
    1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 ≤ exp x := by
  have H := sum_le_exp_of_nonneg hx 8
  have h_eq : ∑ i ∈ range 8, x ^ i / (Nat.factorial i : ℝ) = 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 := by
    simp [sum_range_succ]
    ring
  rwa [h_eq] at H

lemma exp_harmonic_296_lower : (16 * 297 : ℝ) / 9 < exp (harmonic 296) := by
  have h1 : (163 : ℝ) / 26 < (harmonic 296 : ℝ) := by norm_num
  have h2 : exp (163 / 26) < exp (harmonic 296) := exp_lt_exp.mpr h1
  have h3 : (163 : ℝ) / 26 = ((7 : ℕ) : ℝ) * (163 / 182) := by norm_num
  have h4 : exp (163 / 26) = (exp (163 / 182)) ^ 7 := by
    rw [h3, exp_nat_mul]
  have h5 : 1 + 163/182 + (163/182)^2/2 + (163/182)^3/6 + (163/182)^4/24 + (163/182)^5/120 + (163/182)^6/720 + (163/182)^7/5040 ≤ exp (163 / 182) := by
    exact exp_lower_bound_7 _ (by norm_num)
  have h6 : (16 * 297 : ℝ) / 9 < (1 + (163:ℝ)/182 + (163/182)^2/2 + (163/182)^3/6 + (163/182)^4/24 + (163/182)^5/120 + (163/182)^6/720 + (163/182)^7/5040)^7 := by norm_num
  have h7 : (1 + (163:ℝ)/182 + (163/182)^2/2 + (163/182)^3/6 + (163/182)^4/24 + (163/182)^5/120 + (163/182)^6/720 + (163/182)^7/5040)^7 ≤ (exp (163 / 182)) ^ 7 := by
    apply pow_le_pow_left₀
    · positivity
    · exact h5
  linarith

lemma exp_gamma_upper : exp eulerMascheroniConstant < 41 / 23 := by
  have H := eulerMascheroniConstant_lt_eulerMascheroniSeq' 600
  have H2 := exp_lt_exp.mpr H
  have h_seq : eulerMascheroniSeq' 600 = harmonic 600 - Real.log (600:ℝ) := rfl
  rw [h_seq] at H2
  have h3 : exp (harmonic 600 - Real.log (600:ℝ)) = exp (harmonic 600) / 600 := by
    rw [exp_sub, exp_log]; norm_num
  rw [h3] at H2
  have h4 := exp_harmonic_600_upper
  have H_final : exp (harmonic 600) / 600 < (41 * 600 : ℝ) / 23 / 600 := (div_lt_div_iff_of_pos_right (by norm_num)).mpr h4
  have h5 : (41 * 600 : ℝ) / 23 / 600 = 41 / 23 := by norm_num
  rw [h5] at H_final
  exact H2.trans H_final

lemma exp_gamma_lower : 16 / 9 < exp eulerMascheroniConstant := by
  have H := eulerMascheroniSeq_lt_eulerMascheroniConstant 296
  have H2 := exp_lt_exp.mpr H
  have h_seq : eulerMascheroniSeq 296 = harmonic 296 - Real.log (297:ℝ) := by
    change (harmonic 296 : ℝ) - Real.log (((296:ℕ):ℝ) + 1) = (harmonic 296 : ℝ) - Real.log (297:ℝ)
    congr 1
    norm_num
  rw [h_seq] at H2
  have h3 : exp (harmonic 296 - Real.log (297:ℝ)) = exp (harmonic 296) / 297 := by
    rw [exp_sub, exp_log]; norm_num
  rw [h3] at H2
  have h4 := exp_harmonic_296_lower
  have H_final : (16 * 297 : ℝ) / 9 / 297 < exp (harmonic 296) / 297 := (div_lt_div_iff_of_pos_right (by norm_num)).mpr h4
  have h5 : (16 * 297 : ℝ) / 9 / 297 = 16 / 9 := by norm_num
  rw [h5] at H_final
  exact H_final.trans H2

lemma tendsto_floor_exp_harmonic_div_n :
    Tendsto (fun (n : ℕ) => (Int.floor (exp (harmonic n) - 1) : ℝ) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
  have h_H : Tendsto (fun (n : ℕ) => exp (harmonic n) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
    have H := tendsto_harmonic_sub_log
    have H2 := (continuous_exp.tendsto eulerMascheroniConstant).comp H
    apply Tendsto.congr' _ H2
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [Function.comp_apply, exp_sub, exp_log]
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact this
  have h1 : Tendsto (fun n : ℕ => (exp (harmonic n) - 1) / (n : ℝ)) atTop (nhds (exp eulerMascheroniConstant)) := by
    have h_eq : (fun n : ℕ => (exp (harmonic n) - 1) / (n : ℝ)) = fun n : ℕ => exp (harmonic n) / (n : ℝ) - (n : ℝ)⁻¹ := by
      ext n; rw [sub_div, one_div]
    rw [h_eq]
    have h_zero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h_sub := h_H.sub h_zero
    rwa [sub_zero] at h_sub
  have h2 : Tendsto (fun n : ℕ => (exp (harmonic n) - 1) / (n : ℝ) - (n : ℝ)⁻¹) atTop (nhds (exp eulerMascheroniConstant)) := by
    have h_zero : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h_sub := h1.sub h_zero
    rwa [sub_zero] at h_sub
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h_fl := Int.sub_one_lt_floor (exp (harmonic n) - 1)
    have : exp (harmonic n) - 1 - 1 < (Int.floor (exp (harmonic n) - 1) : ℝ) := h_fl
    have h_div : (exp (harmonic n) - 1 - 1) / (n : ℝ) ≤ (Int.floor (exp (harmonic n) - 1) : ℝ) / (n : ℝ) := div_le_div_of_nonneg_right this.le hn_pos.le
    have h_eq : (exp (harmonic n) - 1 - 1) / (n : ℝ) = (exp (harmonic n) - 1) / (n : ℝ) - (n : ℝ)⁻¹ := by
      rw [sub_div, one_div]
    rwa [h_eq] at h_div
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h_fl := Int.floor_le (exp (harmonic n) - 1)
    exact div_le_div_of_nonneg_right h_fl hn_pos.le




lemma harm_mono_real : Monotone (fun n => (harmonic n : ℝ)) := by
  intro a b hab
  induction' b, hab using Nat.le_induction with k hk ih
  · rfl
  · have h_k : (harmonic k : ℝ) ≤ (harmonic (k + 1) : ℝ) := by
      rw [harmonic_succ]
      push_cast
      exact le_add_of_nonneg_right (by positivity)
    exact ih.trans h_k

lemma A206911_mono : Monotone A206911 := by
  intro a b hab
  rw [A206911_eq, A206911_eq]
  have h1 : (harmonic a : ℝ) ≤ (harmonic b : ℝ) := harm_mono_real hab
  have h2 : exp (harmonic a) ≤ exp (harmonic b) := Real.exp_monotone h1
  have h3 : exp (harmonic a) - 1 ≤ exp (harmonic b) - 1 := by linarith
  have h4 : ⌊exp (harmonic a) - 1⌋₊ ≤ ⌊exp (harmonic b) - 1⌋₊ := by
    have h_fl : ⌊exp (harmonic a) - 1⌋ ≤ ⌊exp (harmonic b) - 1⌋ := Int.floor_mono h3
    exact Int.toNat_le_toNat h_fl
  exact Nat.add_le_add hab h4

lemma sum_diff_eq (N : ℕ) : (range N).sum (fun n => A206911_diff (n + 1)) = A206911 (N + 1) - A206911 1 := by
  induction' N with N ih
  · simp
  · rw [sum_range_succ, ih]
    have h1 : A206911 1 ≤ A206911 (N + 1) := A206911_mono (Nat.le_add_left 1 N)
    have h2 : A206911 (N + 1) ≤ A206911 (N + 1 + 1) := A206911_mono (Nat.le_succ _)
    change A206911 (N + 1) - A206911 1 + (A206911 (N + 1 + 1) - A206911 (N + 1)) = A206911 (N + 1 + 1) - A206911 1
    omega



lemma c1_gt_1 : 1 < exp (harmonic 1) * (exp (1 / 2 : ℝ) - 1) := by
  have H : (5:ℝ)/2 ≤ exp 1 := by
    have : (1:ℝ) = 1 := rfl
    have H2 := exp_lower_bound_7 1 (by positivity)
    linarith
  have H2 : 1 + 1/2 + 1/8 ≤ exp (1/2 : ℝ) := by
    have H3 := exp_lower_bound_7 (1/2) (by positivity)
    linarith
  have hh : (harmonic 1 : ℝ) = 1 := by norm_num
  rw [hh]
  calc
    1 = (5/2 : ℝ) * (13/8 - 1) - 9/16 := by norm_num
    _ < (5/2 : ℝ) * (13/8 - 1) := by linarith
    _ ≤ exp 1 * (1 + 1/2 + 1/8 - 1) := by
      apply mul_le_mul H (by linarith) (by norm_num) (exp_pos _).le
    _ ≤ exp 1 * (exp (1/2 : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le

lemma c_lt_2 (n : ℕ) (hn : 1 ≤ n) : exp (harmonic (n + 1)) - exp (harmonic n) < 2 := by
  by_cases h600 : n < 600
  · have h_le : exp (harmonic (n + 1)) - exp (harmonic n) ≤ exp (harmonic (600 + 1)) - exp (harmonic 600) := by
      have h_mono_c := c_mono_le (c := fun k => exp (harmonic (k + 1)) - exp (harmonic k)) ?_ n 600 hn h600.le
      · exact h_mono_c
      · intro k hk
        have h_k : exp (harmonic (k + 1)) - exp (harmonic k) ≤ exp (harmonic (k + 2)) - exp (harmonic (k + 1)) := by
          have h_eq1 : exp (harmonic (k + 1)) - exp (harmonic k) = exp (harmonic k) * (exp (1 / (k + 1 : ℝ)) - 1) := by
            have h1 : (harmonic (k + 1) : ℝ) = harmonic k + (k + 1 : ℝ)⁻¹ := by rw [harmonic_succ]; push_cast; rfl
            rw [h1, one_div, exp_add]; ring
          have h_eq2 : exp (harmonic (k + 2)) - exp (harmonic (k + 1)) = exp (harmonic (k + 1)) * (exp (1 / (k + 2 : ℝ)) - 1) := by
            have h2 : (harmonic (k + 1 + 1) : ℝ) = harmonic (k + 1) + (k + 2 : ℝ)⁻¹ := by
              rw [harmonic_succ]; push_cast; congr 1; ring
            rw [h2, one_div, exp_add]; ring
          rw [h_eq1, h_eq2]
          exact (c_mono k hk).le
        exact h_k
    have h_upper : exp (harmonic (600 + 1)) - exp (harmonic 600) < exp (harmonic (600 + 1)) / (600 + 1 : ℝ) := c_upper_bound 600
    have h_600 : exp (harmonic (600 + 1)) / (600 + 1 : ℝ) < exp (harmonic 600) / 600 := by
      have h_anti := exp_harmonic_div_n_anti 600 (by decide)
      exact_mod_cast h_anti
    have hc : exp (harmonic 600) / 600 < 2 := by
      have h_600_val := exp_harmonic_600_upper
      linarith
    linarith
  · push_neg at h600
    have h_upper : exp (harmonic (n + 1)) - exp (harmonic n) < exp (harmonic (n + 1)) / (n + 1 : ℝ) := c_upper_bound n
    have h_anti : exp (harmonic (n + 1)) / (n + 1 : ℝ) ≤ exp (harmonic 600) / 600 := by
      have h := exp_harmonic_div_n_le_600 (n + 1) (by omega)
      exact_mod_cast h
    have hc : exp (harmonic 600) / 600 < 2 := by
      have h_600_val := exp_harmonic_600_upper
      linarith
    linarith

lemma A206911_diff_eq_2_or_3 (n : ℕ) (hn : 1 ≤ n) : A206911_diff n = 2 ∨ A206911_diff n = 3 := by
  dsimp [A206911_diff]
  rw [A206911_eq, A206911_eq]
  have h_bound : 1 < exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) ∧ exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) < 2 := by
    constructor
    · have hc_base : 1 < exp (harmonic 1) * (exp (1 / (1 + 1 : ℝ)) - 1) := by
        have h2 : ((1:ℝ) + 1) = 2 := by norm_num
        rw [h2]
        exact c1_gt_1
      have h_cn := c_mono_le (c := fun k => exp (harmonic k) * (exp (1 / ((k:ℝ) + 1)) - 1)) ?_ 1 n (by omega) hn
      · have h_harm : exp (harmonic n) * (exp (1 / ((n:ℝ) + 1)) - 1) = exp (harmonic (n + 1)) - exp (harmonic n) := by
          have h1 : (harmonic (n + 1) : ℝ) = harmonic n + ((n:ℝ) + 1)⁻¹ := by rw [harmonic_succ]; push_cast; rfl
          rw [h1, one_div, exp_add]
          ring
        have : exp (harmonic (n + 1)) - 1 - (exp (harmonic n) - 1) = exp (harmonic n) * (exp (1 / ((n:ℝ) + 1)) - 1) := by
          rw [h_harm]
          ring
        rw [this]
        have hc1 : ((1:ℕ):ℝ) = (1:ℝ) := by push_cast; rfl
        dsimp at h_cn
        rw [hc1] at h_cn
        exact hc_base.trans_le h_cn
      · intro k hk
        dsimp
        have h_k : exp (harmonic k) * (exp (1 / ((k:ℝ) + 1)) - 1) ≤ exp (harmonic (k + 1)) * (exp (1 / ((k:ℝ) + 1 + 1)) - 1) := by
          have h1 : ((k:ℝ) + 1 + 1) = (k + 2 : ℝ) := by ring
          rw [h1]
          have h_cast1 : (k:ℝ) + 1 = (k + 1 : ℝ) := by push_cast; rfl
          rw [h_cast1]
          exact (c_mono k hk).le
        have hc : ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; rfl
        rw [hc]
        exact h_k
    · have hc2 : exp (harmonic (n + 1)) - exp (harmonic n) < 2 := c_lt_2 n hn
      linarith
  have h_pos1 : 0 ≤ exp (harmonic n) - 1 := by
    have : 1 ≤ exp (harmonic n) := by
      have h_zero : exp 0 ≤ exp (harmonic n) := Real.exp_monotone (harm_nonneg n)
      rwa [Real.exp_zero] at h_zero
    linarith
  have h_pos2 : 0 ≤ exp (harmonic (n + 1)) - 1 := by
    have : 1 ≤ exp (harmonic (n + 1)) := by
      have h_zero : exp 0 ≤ exp (harmonic (n + 1)) := Real.exp_monotone (harm_nonneg (n + 1))
      rwa [Real.exp_zero] at h_zero
    linarith
  have H := diff_eq_2_or_3 (x := exp (harmonic (n + 1)) - 1) (y := exp (harmonic n) - 1) h_pos1 h_pos2 h_bound
  have h_eq : (n + 1 + ⌊exp (harmonic (n + 1)) - 1⌋₊) - (n + ⌊exp (harmonic n) - 1⌋₊) = 1 + ⌊exp (harmonic (n + 1)) - 1⌋₊ - ⌊exp (harmonic n) - 1⌋₊ := by
    have h1 : (harmonic n : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
      have h_succ : (harmonic (n + 1) : ℝ) = harmonic n + ((n:ℝ) + 1)⁻¹ := by rw [harmonic_succ]; push_cast; rfl
      rw [h_succ]
      exact le_add_of_nonneg_right (by positivity)
    have h2 : exp (harmonic n) - 1 ≤ exp (harmonic (n + 1)) - 1 := by
      have := Real.exp_monotone h1
      linarith
    have h3 : ⌊exp (harmonic n) - 1⌋ ≤ ⌊exp (harmonic (n + 1)) - 1⌋ := Int.floor_mono h2
    have h4 : ⌊exp (harmonic n) - 1⌋₊ ≤ ⌊exp (harmonic (n + 1)) - 1⌋₊ := Int.toNat_le_toNat h3
    omega
  rwa [h_eq]

lemma limit_bounds (E : ℝ) (hE1 : 16/9 < E) (hE2 : E < 41/23) :
    35/10 < (E - 1) / (2 - E) ∧ (E - 1) / (2 - E) < 36/10 := by
  have : 2 - E > 0 := by linarith
  constructor
  · rw [lt_div_iff₀ this]
    linarith
  · rw [div_lt_iff₀ this]
    linarith

lemma count_2s_add_count_3s_eq_N (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    A206911_count_2s N + A206911_count_3s N = N := by
  dsimp [A206911_count_2s, A206911_count_3s]
  rw [← sum_add_distrib]
  have : ∀ n ∈ range N, (if A206911_diff (n + 1) = 2 then 1 else 0) + (if A206911_diff (n + 1) = 3 then 1 else 0) = 1 := by
    intro n _
    rcases h23 (n + 1) (Nat.le_add_left 1 n) with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [sum_congr rfl this, sum_const, card_range, smul_eq_mul, mul_one]

lemma sum_diff_eq_counts (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    (range N).sum (fun n => A206911_diff (n + 1)) = 2 * A206911_count_2s N + 3 * A206911_count_3s N := by
  dsimp [A206911_count_2s, A206911_count_3s]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  have : ∀ n ∈ range N, A206911_diff (n + 1) = 2 * (if A206911_diff (n + 1) = 2 then 1 else 0) + 3 * (if A206911_diff (n + 1) = 3 then 1 else 0) := by
    intro n _
    rcases h23 (n + 1) (Nat.le_add_left 1 n) with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [sum_congr rfl this]

lemma count_3s_eq (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    A206911_count_3s N = (range N).sum (fun n => A206911_diff (n + 1)) - 2 * N := by
  have h2 := sum_diff_eq_counts N h23
  have h3 := count_2s_add_count_3s_eq_N N h23
  omega

lemma count_2s_eq (N : ℕ) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    A206911_count_2s N = 3 * N - (range N).sum (fun n => A206911_diff (n + 1)) := by
  have h2 := sum_diff_eq_counts N h23
  have h3 := count_2s_add_count_3s_eq_N N h23
  omega

lemma tendsto_A206911_div_n : Tendsto (fun n : ℕ => (A206911 n : ℝ) / n) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_floor_exp_harmonic_div_n.const_add 1
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [A206911_eq]
  push_cast
  rw [add_div, div_self (Nat.cast_ne_zero.mpr hn)]
  congr 2
  have h_nonneg : 0 ≤ exp (harmonic n) - 1 := by
    have h_harm_nonneg : (0 : ℝ) ≤ harmonic n := harm_nonneg n
    have : 1 ≤ exp (harmonic n) := by
      have h_exp := Real.exp_monotone h_harm_nonneg
      rwa [Real.exp_zero] at h_exp
    linarith
  have h_fl : (⌊exp (harmonic n) - 1⌋₊ : ℤ) = ⌊exp (harmonic n) - 1⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr h_nonneg)
  rw [← Int.cast_natCast ⌊exp (harmonic n) - 1⌋₊, h_fl]

lemma tendsto_A206911_succ_div_N : Tendsto (fun N : ℕ => (A206911 (N + 1) : ℝ) / N) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_A206911_div_n
  have H1 := H.comp (tendsto_add_atTop_nat 1)
  have H2 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 1) := by
    have H2a : Tendsto (fun N : ℕ => 1 + (N : ℝ)⁻¹) atTop (nhds 1) := by
      have hz : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have ha := hz.const_add 1
      rwa [add_zero] at ha
    apply Tendsto.congr' _ H2a
    filter_upwards [eventually_ne_atTop 0] with N hN
    push_cast
    rw [add_div, div_self (Nat.cast_ne_zero.mpr hN), one_div]
  have H3 := H1.mul H2
  rw [mul_one] at H3
  apply Tendsto.congr' _ H3
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hn_ne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp
  have : ((A206911 (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ)) * (((N + 1 : ℕ) : ℝ) / (N : ℝ)) = (A206911 (N + 1) : ℝ) / (N : ℝ) := by
    calc
      _ = (A206911 (N + 1) : ℝ) * ((N + 1 : ℕ) : ℝ)⁻¹ * (((N + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹) := by rw [div_eq_mul_inv, div_eq_mul_inv]
      _ = (A206911 (N + 1) : ℝ) * (((N + 1 : ℕ) : ℝ)⁻¹ * ((N + 1 : ℕ) : ℝ)) * (N : ℝ)⁻¹ := by ring
      _ = (A206911 (N + 1) : ℝ) * 1 * (N : ℝ)⁻¹ := by rw [inv_mul_cancel₀ hn_ne]
      _ = (A206911 (N + 1) : ℝ) / (N : ℝ) := by rw [mul_one, ← div_eq_mul_inv]
  exact this

lemma tendsto_A206911_1_div_N : Tendsto (fun N : ℕ => (A206911 1 : ℝ) / N) atTop (nhds 0) := by
  have : (fun N : ℕ => (A206911 1 : ℝ) / N) = fun N : ℕ => (A206911 1 : ℝ) * (N : ℝ)⁻¹ := by
    ext N
    rw [div_eq_mul_inv]
  rw [this]
  have hz : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hz.const_mul (A206911 1 : ℝ)
  rwa [mul_zero] at h

lemma tendsto_sum_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) / N) atTop (nhds (1 + exp eulerMascheroniConstant)) := by
  have H := tendsto_A206911_succ_div_N.sub tendsto_A206911_1_div_N
  rw [sub_zero] at H
  apply Tendsto.congr' _ H
  filter_upwards [] with N
  have h_sum := sum_diff_eq N
  have h_sum_real : ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) = (A206911 (N + 1) : ℝ) - (A206911 1 : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sub (h_mono (Nat.le_add_left 1 N)), ← h_sum]
  rw [h_sum_real]
  push_cast
  rw [sub_div]

lemma tendsto_c3_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / N) atTop (nhds (exp eulerMascheroniConstant - 1)) := by
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have H := (tendsto_sum_div_N h_mono h23).sub hc2
  have eq : 1 + exp eulerMascheroniConstant - 2 = exp eulerMascheroniConstant - 1 := by ring
  rw [eq] at H
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  have h_c3 := count_3s_eq N h23
  have h2 : 2 * N ≤ (range N).sum (fun n => A206911_diff (n + 1)) := by
    have h2' : (range N).sum (fun _ => 2) ≤ (range N).sum (fun n => A206911_diff (n + 1)) := by
      apply sum_le_sum
      intro i _
      rcases h23 (i + 1) (Nat.le_add_left 1 i) with h | h
      · rw [h]
      · rw [h]; omega
    simp at h2'
    rw [mul_comm] at h2'
    exact h2'
  have h_cast : (A206911_count_3s N : ℝ) = ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) - 2 * N := by
    rw [h_c3, Nat.cast_sub h2, ← Nat.cast_sum]; push_cast; rfl
  rw [h_cast, sub_div]
  congr 1
  rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]

lemma tendsto_c2_div_N (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) :
    Tendsto (fun N : ℕ => (A206911_count_2s N : ℝ) / N) atTop (nhds (2 - exp eulerMascheroniConstant)) := by
  have hc3 : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) := tendsto_const_nhds
  have H := hc3.sub (tendsto_sum_div_N h_mono h23)
  have eq : 3 - (1 + exp eulerMascheroniConstant) = 2 - exp eulerMascheroniConstant := by ring
  rw [eq] at H
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  have h_c2 := count_2s_eq N h23
  have h3 : (range N).sum (fun n => A206911_diff (n + 1)) ≤ 3 * N := by
    have h3' : (range N).sum (fun n => A206911_diff (n + 1)) ≤ (range N).sum (fun _ => 3) := by
      apply sum_le_sum
      intro i _
      rcases h23 (i + 1) (Nat.le_add_left 1 i) with h | h
      · rw [h]; omega
      · rw [h]
    simp at h3'
    rw [mul_comm] at h3'
    exact h3'
  have h_cast : (A206911_count_2s N : ℝ) = 3 * N - ((range N).sum (fun n => A206911_diff (n + 1)) : ℝ) := by
    rw [h_c2, Nat.cast_sub h3, ← Nat.cast_sum]; push_cast; rfl
  rw [h_cast, sub_div]
  congr 1
  rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]

lemma tendsto_ratio (h_mono : Monotone A206911) (h23 : ∀ n, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) (h_not_two : exp eulerMascheroniConstant ≠ 2) :
    Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds ((exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant))) := by
  have H := (tendsto_c3_div_N h_mono h23).div (tendsto_c2_div_N h_mono h23) (by exact sub_ne_zero.mpr h_not_two.symm)
  apply Tendsto.congr' _ H
  filter_upwards [eventually_ne_atTop 0] with N hn
  dsimp
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) (A206911_count_3s N : ℝ) (A206911_count_2s N : ℝ)



theorem oeis_206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L))
:= by
  have h23 : ∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3 := A206911_diff_eq_2_or_3
  constructor
  · exact h23
  · use (exp eulerMascheroniConstant - 1) / (2 - exp eulerMascheroniConstant)
    constructor
    · have hL := limit_bounds (exp eulerMascheroniConstant) exp_gamma_lower exp_gamma_upper
      exact hL.1
    · constructor
      · have hL := limit_bounds (exp eulerMascheroniConstant) exp_gamma_lower exp_gamma_upper
        exact hL.2
      · have h_not_two : exp eulerMascheroniConstant ≠ 2 := by
          have h_up := exp_gamma_upper
          linarith
        exact tendsto_ratio A206911_mono h23 h_not_two

theorem oeis_206911_conjecture.disproof : ¬ (type_of% @oeis_206911_conjecture) := sorry
