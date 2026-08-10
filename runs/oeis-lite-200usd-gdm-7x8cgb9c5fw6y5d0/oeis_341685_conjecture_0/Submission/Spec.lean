import FormalConjectures.Util.ProblemImports

open Nat BigOperators
open Filter Topology
open Polynomial

/--
The $p$-adic numbers `Padic p` require `p` to be a prime.
We assert this fact for $p=3$.
-/
instance : Fact (Nat.Prime 3) := by
  constructor
  norm_num

/--
The $m$-th successive approximation of the 3-adic integer $\sum_{k \ge 0} k!$.
This is $X_m = \left(\sum_{k=0}^\infty k!\right) \bmod 3^m$, computed here using a truncated sum since $\nu_3(k!)$ grows quickly.
We use a safe upper bound of $3m-1$ for the summation.
-/
def approx_3_adic_sum_factorial (m : ℕ) : ℕ :=
  let p := 3
  if m = 0 then 0
  else
    -- The upper limit for the sum is $p \cdot m$.
    let upper_k := p * m
    (Finset.range upper_k).sum Nat.factorial % (p ^ m)

/--
A341685: Expansion of the 3-adic integer $\sum_{k\ge 0} k!$.
The $n$-th digit $a(n)$ is the coefficient of $3^n$.
$$a(n) = \frac{\left(\sum_{k=0}^\infty k!\right) \bmod 3^{n+1} - \left(\sum_{k=0}^\infty k!\right) \bmod 3^n}{3^n}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p := 3
  let X_n_plus_1 := approx_3_adic_sum_factorial (n + 1)
  let X_n := approx_3_adic_sum_factorial n

  -- The subtraction is safe because $X_{n+1} \ge X_n$.
  (X_n_plus_1 - X_n) / (p ^ n)

lemma test_tendsto_zero {F : Filter ℕ} {f : ℕ → Padic 3} :
  Tendsto f F (𝓝 0) ↔ Tendsto (fun x => ‖f x‖) F (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero

lemma norm_factorial_le_iff_dvd (k N : ℕ) :
  ‖(Nat.factorial k : Padic 3)‖ ≤ (3 : ℝ) ^ (- (N : ℤ)) ↔ 3 ^ N ∣ Nat.factorial k := by
  have h1 : (Nat.factorial k : Padic 3) = ((Nat.factorial k : ℤ) : Padic 3) := by norm_cast
  have h2 : 3 ^ N ∣ Nat.factorial k ↔ (3 : ℤ) ^ N ∣ (Nat.factorial k : ℤ) := by norm_cast
  rw [h1, h2]
  exact Padic.norm_int_le_pow_iff_dvd (Nat.factorial k) N

lemma tendsto_pow_three_neg : Tendsto (fun N : ℕ => (3 : ℝ) ^ (- (N : ℤ))) atTop (𝓝 0) := by
  have h_eq : (fun N : ℕ => (3 : ℝ) ^ (- (N : ℤ))) = (fun N : ℕ => ((3 : ℝ)⁻¹) ^ N) := by
    ext N
    simp only [zpow_neg, zpow_natCast, inv_pow]
  rw [h_eq]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · norm_num
  · norm_num

lemma tendsto_zero_of_pow_neg_tendsto {f : ℕ → ℝ} (hnonneg : ∀ k, 0 ≤ f k)
  (h : ∀ N : ℕ, ∃ K : ℕ, ∀ k ≥ K, f k ≤ (3 : ℝ) ^ (- (N : ℤ))) :
  Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_lim := tendsto_pow_three_neg
  rw [Metric.tendsto_atTop] at h_lim
  rcases h_lim ε hε with ⟨N1, hN1⟩
  rcases h N1 with ⟨K, hK⟩
  use K
  intro k hk
  have h_dist : dist (f k) 0 = f k := by
    rw [Real.dist_0_eq_abs, abs_of_nonneg (hnonneg k)]
  rw [h_dist]
  have h_pow_dist : dist ((3 : ℝ) ^ (- (N1 : ℤ))) 0 = (3 : ℝ) ^ (- (N1 : ℤ)) := by
    rw [Real.dist_0_eq_abs, abs_of_nonneg]
    positivity
  have h_lt_ε : (3 : ℝ) ^ (- (N1 : ℤ)) < ε := by
    have h_lt_ε_dist := hN1 N1 le_rfl
    rwa [h_pow_dist] at h_lt_ε_dist
  exact lt_of_le_of_lt (hK k hk) h_lt_ε

lemma padicValNat_mono_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
  padicValNat 3 a ≤ padicValNat 3 b := by
  have hdvd : 3 ^ padicValNat 3 a ∣ b := (pow_padicValNat_dvd (p := 3)).trans h
  rwa [padicValNat_dvd_iff_le hb] at hdvd

lemma three_pow_dvd_factorial (N k : ℕ) (h : 3 * N ≤ k) : 3 ^ N ∣ Nat.factorial k := by
  have hk0 : Nat.factorial k ≠ 0 := Nat.factorial_ne_zero k
  rw [padicValNat_dvd_iff_le hk0]
  have h_dvd : (3 * N).factorial ∣ k.factorial := Nat.factorial_dvd_factorial h
  have h_mono := padicValNat_mono_of_dvd hk0 h_dvd
  have h_mul : padicValNat 3 (3 * N).factorial = padicValNat 3 N.factorial + N := by
    exact padicValNat_factorial_mul N
  have h_ge : N ≤ padicValNat 3 (3 * N).factorial := by
    rw [h_mul]
    exact Nat.le_add_left N (padicValNat 3 N.factorial)
  exact h_ge.trans h_mono

lemma summable_factorial : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [test_tendsto_zero]
  rw [Nat.cofinite_eq_atTop]
  apply tendsto_zero_of_pow_neg_tendsto
  · intro k
    exact norm_nonneg _
  · intro N
    use 3 * N
    intro k hk
    rw [norm_factorial_le_iff_dvd]
    exact three_pow_dvd_factorial N k hk

/--
The 3-adic constant $\xi_3 = \sum_{k \ge 0} k!$.
This series converges in `Padic 3`.
-/
noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

open Algebra

noncomputable def s (n : ℕ) : Padic 3 :=
  ∑ i ∈ Finset.range (n + 1), (Nat.factorial i : Padic 3)

lemma norm_natCast_le_one (c : ℕ) : ‖(c : Padic 3)‖ ≤ 1 := by
  have h1 : (c : Padic 3) = ((c : ℤ) : Padic 3) := by norm_cast
  rw [h1]
  exact Padic.norm_int_le_one c

lemma norm_le_norm_of_dvd {a b : ℕ} (h : a ∣ b) : ‖(b : Padic 3)‖ ≤ ‖(a : Padic 3)‖ := by
  rcases h with ⟨c, rfl⟩
  rw [Nat.cast_mul, norm_mul]
  have hc := norm_natCast_le_one c
  have ha_nonneg : 0 ≤ ‖(a : Padic 3)‖ := norm_nonneg _
  nlinarith

lemma norm_factorial_le (i n : ℕ) : ‖((i + n + 1).factorial : Padic 3)‖ ≤ ‖((n + 1).factorial : Padic 3)‖ := by
  apply norm_le_norm_of_dvd
  apply Nat.factorial_dvd_factorial
  omega

lemma norm_tsum_factorial_le (n : ℕ) : ‖∑' i : ℕ, ((i + n + 1).factorial : Padic 3)‖ ≤ ‖((n + 1).factorial : Padic 3)‖ := by
  have h1 := IsUltrametricDist.norm_tsum_le (fun i => ((i + n + 1).factorial : Padic 3))
  have h2 : (⨆ i : ℕ, ‖((i + n + 1).factorial : Padic 3)‖) ≤ ‖((n + 1).factorial : Padic 3)‖ := by
    apply ciSup_le
    intro i
    exact norm_factorial_le i n
  exact h1.trans h2

lemma tsum_eq_s_add_tsum (n : ℕ) :
  xi_3 = s n + ∑' i : ℕ, ((i + n + 1).factorial : Padic 3) := by
  have h_split := Summable.sum_add_tsum_nat_add (n + 1) summable_factorial
  change s n + ∑' i : ℕ, ((i + (n + 1)).factorial : Padic 3) = xi_3 at h_split
  have h_eq_arith : (fun i : ℕ => ((i + n + 1).factorial : Padic 3)) = (fun i : ℕ => ((i + (n + 1)).factorial : Padic 3)) := by
    ext i
    congr 2
  rw [h_eq_arith]
  exact h_split.symm

lemma norm_xi_3_sub_s_le (n : ℕ) : ‖xi_3 - s n‖ ≤ ‖((n + 1).factorial : Padic 3)‖ := by
  rw [tsum_eq_s_add_tsum n]
  have h_sub : (s n + ∑' i : ℕ, ((i + n + 1).factorial : Padic 3)) - s n = ∑' i : ℕ, ((i + n + 1).factorial : Padic 3) := by
    ring
  rw [h_sub]
  exact norm_tsum_factorial_le n

lemma norm_add_eq_max_of_norm_ne {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (x y : E) (h : ‖x‖ ≠ ‖y‖) :
  ‖x + y‖ = max ‖x‖ ‖y‖ := by
  have h_dist : dist (x + y) 0 = ‖x + y‖ := by rw [_root_.dist_zero_right]
  have h_dist_x : dist (x + y) y = ‖x‖ := by
    rw [dist_eq_norm]
    simp
  have h_dist_y : dist y 0 = ‖y‖ := by rw [_root_.dist_zero_right]
  have h_ne : dist (x + y) y ≠ dist y 0 := by
    rwa [h_dist_x, h_dist_y]
  have h_max := IsUltrametricDist.dist_eq_max_of_dist_ne_dist (x + y) y 0 h_ne
  rwa [h_dist, h_dist_x, h_dist_y] at h_max

lemma s_one : s 1 = 2 := by
  unfold s
  simp [Finset.sum_range_succ]
  ring

lemma s_two : s 2 = 4 := by
  unfold s
  simp [Finset.sum_range_succ]
  ring

lemma s_five : s 5 = 154 := by
  unfold s
  simp [Finset.sum_range_succ]
  ring

lemma R_2_split :
  ∑' i : ℕ, ((i + 2).factorial : Padic 3) = 2 + ∑' i : ℕ, ((i + 3).factorial : Padic 3) := by
  have h1 := tsum_eq_s_add_tsum 1
  have h2 := tsum_eq_s_add_tsum 2
  rw [s_one] at h1
  rw [s_two] at h2
  rw [h1] at h2
  generalize ∑' i : ℕ, ((i + 2).factorial : Padic 3) = R2 at h2 ⊢
  generalize ∑' i : ℕ, ((i + 3).factorial : Padic 3) = R3 at h2 ⊢
  calc R2
    _ = (4 + R3) - 2 := by rw [← h2]; ring
    _ = 2 + R3 := by ring

lemma h_sub_eq (a b : ℤ) (h : (b : Padic 3) * xi_3 = a) :
  (b : Padic 3) * ∑' i : ℕ, ((i + 2).factorial : Padic 3) = (a : Padic 3) - 2 * (b : Padic 3) := by
  have h_split := tsum_eq_s_add_tsum 1
  rw [s_one] at h_split
  rw [h_split] at h
  rw [mul_add] at h
  generalize ∑' i : ℕ, ((i + 2).factorial : Padic 3) = R at h ⊢
  have h_id : (b : Padic 3) * 2 = 2 * (b : Padic 3) := by ring
  rw [h_id] at h
  calc (b : Padic 3) * R
    _ = (a : Padic 3) - 2 * (b : Padic 3) := by
      rw [← h]
      ring

lemma h_R3_eq (a b : ℤ) (h : (b : Padic 3) * xi_3 = a) :
  (b : Padic 3) * ∑' i : ℕ, ((i + 3).factorial : Padic 3) = (a : Padic 3) - 4 * (b : Padic 3) := by
  have h2 := h_sub_eq a b h
  rw [R_2_split] at h2
  rw [mul_add] at h2
  generalize ∑' i : ℕ, ((i + 3).factorial : Padic 3) = R3 at h2 ⊢
  have h_id : (b : Padic 3) * 2 = 2 * (b : Padic 3) := by ring
  rw [h_id] at h2
  calc (b : Padic 3) * R3
    _ = (2 * (b : Padic 3) + (b : Padic 3) * R3) - 2 * (b : Padic 3) := by ring
    _ = (a : Padic 3) - 2 * (b : Padic 3) - 2 * (b : Padic 3) := by rw [h2]
    _ = (a : Padic 3) - 4 * (b : Padic 3) := by ring

lemma norm_six_le : ‖(6 : Padic 3)‖ ≤ 1 / 3 := by
  have h_eq : (6 : Padic 3) = ((6 : ℤ) : Padic 3) := by norm_cast
  rw [h_eq]
  have h_dvd : (3 : ℤ) ^ 1 ∣ 6 := by norm_num
  have h_le := (Padic.norm_int_le_pow_iff_dvd 6 1).mpr h_dvd
  norm_num at h_le
  exact h_le

lemma norm_R_3_le : ‖∑' i : ℕ, ((i + 3).factorial : Padic 3)‖ ≤ 1 / 3 := by
  have h := norm_tsum_factorial_le 2
  have h3 : ‖((2 + 1).factorial : Padic 3)‖ = ‖(6 : Padic 3)‖ := by rfl
  rw [h3] at h
  exact h.trans norm_six_le

lemma norm_factorial_six_le : ‖((6 : ℕ).factorial : Padic 3)‖ ≤ 1 / 9 := by
  have h_eq : (720 : Padic 3) = ((720 : ℤ) : Padic 3) := by norm_cast
  change ‖(720 : Padic 3)‖ ≤ 1 / 9
  rw [h_eq]
  have h_dvd : (3 : ℤ) ^ 2 ∣ 720 := by norm_num
  have h_le := (Padic.norm_int_le_pow_iff_dvd 720 2).mpr h_dvd
  norm_num at h_le
  exact h_le

lemma norm_R_6_le : ‖∑' i : ℕ, ((i + 6).factorial : Padic 3)‖ ≤ 1 / 9 := by
  have h := norm_tsum_factorial_le 5
  exact h.trans norm_factorial_six_le

lemma R_3_split_three :
  ∑' i : ℕ, ((i + 3).factorial : Padic 3) = 150 + ∑' i : ℕ, ((i + 6).factorial : Padic 3) := by
  have h1 := tsum_eq_s_add_tsum 2
  have h2 := tsum_eq_s_add_tsum 5
  rw [s_two] at h1
  rw [s_five] at h2
  rw [h1] at h2
  generalize ∑' i : ℕ, ((i + 3).factorial : Padic 3) = R3 at h2 ⊢
  generalize ∑' i : ℕ, ((i + 6).factorial : Padic 3) = R6 at h2 ⊢
  calc R3
    _ = (154 + R6) - 4 := by rw [← h2]; ring
    _ = 150 + R6 := by ring

lemma R_3_ne_zero : ∑' i : ℕ, ((i + 3).factorial : Padic 3) ≠ 0 := by
  have h_not_le : ¬ ‖(150 : Padic 3)‖ ≤ 1 / 9 := by
    have h_eq : (150 : Padic 3) = ((150 : ℤ) : Padic 3) := by norm_cast
    rw [h_eq]
    have h_pow : (1 / 9 : ℝ) = (3 : ℝ) ^ (- (2 : ℤ)) := by norm_num
    rw [h_pow]
    intro h_le
    have h_dvd := (Padic.norm_int_le_pow_iff_dvd 150 2).mp h_le
    have h_not_dvd : ¬ (3 : ℤ) ^ 2 ∣ 150 := by norm_num
    exact h_not_dvd h_dvd
  have h_ne : ‖(150 : Padic 3)‖ ≠ ‖∑' i : ℕ, ((i + 6).factorial : Padic 3)‖ := by
    intro h_eq
    have h_le := norm_R_6_le
    rw [← h_eq] at h_le
    exact h_not_le h_le
  have h_norm_eq : ‖∑' i : ℕ, ((i + 3).factorial : Padic 3)‖ = ‖(150 : Padic 3)‖ := by
    rw [R_3_split_three]
    rw [norm_add_eq_max_of_norm_ne 150 (∑' i : ℕ, ((i + 6).factorial : Padic 3)) h_ne]
    rw [max_eq_left]
    have h_le := norm_R_6_le
    have h_150_ge : 1 / 9 < ‖(150 : Padic 3)‖ := by
      exact lt_of_not_ge h_not_le
    exact h_le.trans h_150_ge.le
  intro h_zero
  rw [h_zero, _root_.norm_zero] at h_norm_eq
  have h150_ne_zero : (150 : Padic 3) ≠ 0 := by norm_num
  have h150_norm_ne_zero : ‖(150 : Padic 3)‖ ≠ 0 := (_root_.norm_ne_zero_iff).mpr h150_ne_zero
  exact h150_norm_ne_zero h_norm_eq.symm

lemma poly_split_two {R : Type*} [CommRing R] (q : R[X]) :
  q = C (q.coeff 0) + C (q.coeff 1) * X + X^2 * q.divX.divX := by
  calc q
    _ = X * q.divX + C (q.coeff 0) := by rw [X_mul_divX_add]
    _ = X * (X * q.divX.divX + C (q.coeff 1)) + C (q.coeff 0) := by
      have h := X_mul_divX_add q.divX
      have hc : q.divX.coeff 0 = q.coeff 1 := coeff_divX
      rw [hc] at h
      congr 2
      exact h.symm
    _ = C (q.coeff 0) + C (q.coeff 1) * X + X^2 * q.divX.divX := by ring

lemma eval_taylor_split {R : Type*} [CommRing R] (x y : R) (p : R[X]) :
  eval (x + y) p = eval x p + y * eval x (derivative p) + y^2 * eval y (p.taylor x).divX.divX := by
  have h_taylor : eval y (p.taylor x) = eval (x + y) p := by
    rw [taylor_apply, eval_comp, eval_add, eval_X, eval_C, add_comm]
  have h_split := poly_split_two (p.taylor x)
  have h_eval := congr_arg (eval y) h_split
  rw [h_taylor] at h_eval
  rw [eval_add, eval_add, eval_C, eval_mul, eval_C, eval_X, eval_mul, eval_pow, eval_X] at h_eval
  have h_coeff0 : (p.taylor x).coeff 0 = eval x p := by
    rw [taylor_coeff, hasseDeriv_zero, _root_.LinearMap.id_apply]
  have h_coeff1 : (p.taylor x).coeff 1 = eval x (derivative p) := by
    rw [taylor_coeff, hasseDeriv_one]
  rw [h_coeff0, h_coeff1] at h_eval
  calc eval (x + y) p
    _ = eval x p + eval x (derivative p) * y + y^2 * eval y (p.taylor x).divX.divX := h_eval
    _ = eval x p + y * eval x (derivative p) + y^2 * eval y (p.taylor x).divX.divX := by ring

lemma minimal_poly_derivative_ne_zero (x : Padic 3) (h : IsAlgebraic ℚ x) :
  ∃ p : ℚ[X], p ≠ 0 ∧ aeval x p = 0 ∧ (∀ q : ℚ[X], q ≠ 0 → aeval x q = 0 → p.natDegree ≤ q.natDegree) ∧
    aeval x (derivative p) ≠ 0 := by
  let S := {n : ℕ | ∃ p : ℚ[X], p.natDegree = n ∧ p ≠ 0 ∧ aeval x p = 0}
  have hS : S.Nonempty := by
    rcases h with ⟨p, hp0, hp_eval⟩
    exact ⟨p.natDegree, p, rfl, hp0, hp_eval⟩
  haveI : DecidablePred (fun n => n ∈ S) := fun _ => Classical.dec _
  let n := Nat.find hS
  have hn : n ∈ S := Nat.find_spec hS
  rcases hn with ⟨p, hp_deg, hp0, hp_eval⟩
  have h_min : ∀ q : ℚ[X], q ≠ 0 → aeval x q = 0 → p.natDegree ≤ q.natDegree := by
    intro q hq0 hq_eval
    have hqS : q.natDegree ∈ S := ⟨q, rfl, hq0, hq_eval⟩
    have h_le := Nat.find_le (h := hS) hqS
    rwa [hp_deg]
  use p, hp0, hp_eval, h_min
  intro h_deriv
  have h_deriv_eq_zero : derivative p = 0 := by
    by_cases hd0 : p.natDegree = 0
    · exact derivative_of_natDegree_zero hd0
    · by_cases h_deriv_zero : derivative p = 0
      · exact h_deriv_zero
      · have h_lt : (derivative p).natDegree < p.natDegree := natDegree_derivative_lt hd0
        have h_le := h_min (derivative p) h_deriv_zero h_deriv
        omega
  have h_C := eq_C_of_derivative_eq_zero h_deriv_eq_zero
  rw [h_C] at hp_eval
  rw [aeval_C] at hp_eval
  have h_coeff : p.coeff 0 = 0 := by
    have h_inj : Function.Injective (algebraMap ℚ (Padic 3)) := (algebraMap ℚ (Padic 3)).injective
    exact h_inj hp_eval
  have hp_eq : p = 0 := by
    rw [h_C, h_coeff, C_0]
  exact hp0 hp_eq

lemma map_comp :
  (algebraMap ℚ (Padic 3)).comp (algebraMap ℤ ℚ) = algebraMap ℤ (Padic 3) := by
  ext x
  simp

lemma p_padic_eq_q_padic (p : ℚ[X]) (W : ℤ) (q : ℤ[X]) (hW : W ≠ 0) (hp : p = C (1 / (W : ℚ)) * q.map (algebraMap ℤ ℚ)) :
  p.map (algebraMap ℚ (Padic 3)) = C (1 / (W : Padic 3)) * q.map (algebraMap ℤ (Padic 3)) := by
  rw [hp]
  rw [Polynomial.map_mul, Polynomial.map_C]
  have h_div : (algebraMap ℚ (Padic 3)) (1 / (W : ℚ)) = 1 / (W : Padic 3) := by
    simp
  rw [h_div]
  congr 1
  rw [Polynomial.map_map, _root_.map_comp]

def s_int (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (Nat.factorial i : ℤ)

lemma s_eq_s_int (n : ℕ) : s n = ((s_int n : ℤ) : Padic 3) := by
  unfold s s_int
  push_cast
  rfl

lemma eval_q_padic (q : ℤ[X]) (n : ℕ) :
  eval (s n) (q.map (algebraMap ℤ (Padic 3))) = ((eval (s_int n) q : ℤ) : Padic 3) := by
  rw [s_eq_s_int]
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_hom (algebraMap ℤ (Padic 3)) (s_int n)

lemma s_int_diff (n : ℕ) : s_int (n+1) - s_int n = ((n+1).factorial : ℤ) := by
  unfold s_int
  rw [Finset.sum_range_succ]
  ring

lemma dvd_eval_diff (q : ℤ[X]) (n : ℕ) :
  ((n+1).factorial : ℤ) ∣ eval (s_int (n+1)) q - eval (s_int n) q := by
  have h := Polynomial.sub_dvd_eval_sub (s_int (n+1)) (s_int n) q
  rw [s_int_diff] at h
  exact h

lemma norm_le_norm_of_dvd_int {a b : ℤ} (h : a ∣ b) : ‖(b : Padic 3)‖ ≤ ‖(a : Padic 3)‖ := by
  rcases h with ⟨c, rfl⟩
  rw [Int.cast_mul, norm_mul]
  have hc : ‖(c : Padic 3)‖ ≤ 1 := Padic.norm_int_le_one c
  have ha_nonneg : 0 ≤ ‖(a : Padic 3)‖ := norm_nonneg _
  nlinarith

lemma norm_eval_diff_le (q : ℤ[X]) (n : ℕ) :
  ‖eval (s (n+1)) (q.map (algebraMap ℤ (Padic 3))) - eval (s n) (q.map (algebraMap ℤ (Padic 3)))‖ ≤ ‖((n+1).factorial : Padic 3)‖ := by
  rw [eval_q_padic, eval_q_padic]
  have h_sub : ((eval (s_int (n+1)) q : ℤ) : Padic 3) - ((eval (s_int n) q : ℤ) : Padic 3) = (((eval (s_int (n+1)) q - eval (s_int n) q : ℤ) : Padic 3)) := by
    push_cast
    rfl
  rw [h_sub]
  apply norm_le_norm_of_dvd_int
  exact dvd_eval_diff q n

lemma induction_on_X_mul {R : Type*} [CommRing R] {motive : R[X] → Prop} (p : R[X])
  (C_case : ∀ a, motive (C a))
  (add_case : ∀ p q, motive p → motive q → motive (p + q))
  (X_mul_case : ∀ p, motive p → motive (p * X)) : motive p := by
  refine Polynomial.induction_on p C_case add_case ?_
  intro n a ih
  have h_eq : C a * X ^ (n + 1) = (C a * X ^ n) * X := by
    rw [pow_succ, ← mul_assoc]
  rw [h_eq]
  exact X_mul_case _ ih

lemma clear_denominators (p : ℚ[X]) : ∃ (W : ℤ) (q : ℤ[X]), W ≠ 0 ∧ p = C (1 / (W : ℚ)) * q.map (algebraMap ℤ ℚ) := by
  apply induction_on_X_mul p
  · intro r
    use r.den, C r.num
    refine ⟨by exact_mod_cast r.den_ne_zero, ?_⟩
    rw [Polynomial.map_C]
    rw [← C_mul]
    congr 1
    change r = 1 / (r.den : ℚ) * (r.num : ℚ)
    have h1 : 1 / (r.den : ℚ) * (r.num : ℚ) = (r.num : ℚ) / (r.den : ℚ) := by ring
    rw [h1]
    exact (Rat.num_div_den r).symm
  · intro f g hf hg
    rcases hf with ⟨W_f, q_f, hW_f, hf_eq⟩
    rcases hg with ⟨W_g, q_g, hW_g, hg_eq⟩
    use W_f * W_g, q_f * C W_g + q_g * C W_f
    refine ⟨mul_ne_zero hW_f hW_g, ?_⟩
    rw [hf_eq, hg_eq]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C]
    have h_eq : C (1 / ((W_f * W_g : ℤ) : ℚ)) = C (1 / (W_f : ℚ)) * C (1 / (W_g : ℚ)) := by
      rw [← Polynomial.C_mul]
      congr 1
      push_cast
      have hW_f_q : (W_f : ℚ) ≠ 0 := by exact_mod_cast hW_f
      have hW_g_q : (W_g : ℚ) ≠ 0 := by exact_mod_cast hW_g
      field_simp
    rw [h_eq]
    have h_alg_f : C ((algebraMap ℤ ℚ) W_f) = C (W_f : ℚ) := rfl
    have h_alg_g : C ((algebraMap ℤ ℚ) W_g) = C (W_g : ℚ) := rfl
    rw [h_alg_f, h_alg_g]
    have h_inv_f : C (1 / (W_f : ℚ)) * C (W_f : ℚ) = 1 := by
      rw [← Polynomial.C_mul]
      have hW_f_q : (W_f : ℚ) ≠ 0 := by exact_mod_cast hW_f
      rw [one_div_mul_cancel hW_f_q]
      rw [Polynomial.C_1]
    have h_inv_g : C (1 / (W_g : ℚ)) * C (W_g : ℚ) = 1 := by
      rw [← Polynomial.C_mul]
      have hW_g_q : (W_g : ℚ) ≠ 0 := by exact_mod_cast hW_g
      rw [one_div_mul_cancel hW_g_q]
      rw [Polynomial.C_1]
    symm
    calc
      C (1 / (W_f : ℚ)) * C (1 / (W_g : ℚ)) * (q_f.map (algebraMap ℤ ℚ) * C (W_g : ℚ) + q_g.map (algebraMap ℤ ℚ) * C (W_f : ℚ))
      _ = (C (1 / (W_f : ℚ)) * q_f.map (algebraMap ℤ ℚ)) * (C (1 / (W_g : ℚ)) * C (W_g : ℚ)) +
          (C (1 / (W_g : ℚ)) * q_g.map (algebraMap ℤ ℚ)) * (C (1 / (W_f : ℚ)) * C (W_f : ℚ)) := by ring
      _ = C (1 / (W_f : ℚ)) * q_f.map (algebraMap ℤ ℚ) + C (1 / (W_g : ℚ)) * q_g.map (algebraMap ℤ ℚ) := by
        rw [h_inv_g, h_inv_f]
        ring
  · intro f hf
    rcases hf with ⟨W_f, q_f, hW_f, hf_eq⟩
    use W_f, q_f * X
    refine ⟨hW_f, ?_⟩
    rw [hf_eq]
    rw [Polynomial.map_mul, Polynomial.map_X]
    ring

lemma tendsto_s : Tendsto s atTop (𝓝 xi_3) := by
  have h := summable_factorial.hasSum.tendsto_sum_nat
  have h_shift := Tendsto.comp h (tendsto_add_atTop_nat 1)
  exact h_shift

lemma tendsto_eval_s (q : ℤ[X]) :
  Tendsto (fun n => eval (s n) (q.map (algebraMap ℤ (Padic 3)))) atTop (𝓝 (eval xi_3 (q.map (algebraMap ℤ (Padic 3))))) := by
  have h_cont := (q.map (algebraMap ℤ (Padic 3))).continuous
  exact (Continuous.tendsto h_cont xi_3).comp tendsto_s

lemma eval_q_padic_xi_3 (p : ℚ[X]) (W : ℤ) (q : ℤ[X]) (hW : W ≠ 0)
  (hp : p = C (1 / (W : ℚ)) * q.map (algebraMap ℤ ℚ)) (hp_eval : aeval xi_3 p = 0) :
  eval xi_3 (q.map (algebraMap ℤ (Padic 3))) = 0 := by
  have hp_padic := p_padic_eq_q_padic p W q hW hp
  have h_eval : eval xi_3 (p.map (algebraMap ℚ (Padic 3))) = 0 := by
    rw [Polynomial.eval_map]
    exact hp_eval
  rw [hp_padic] at h_eval
  rw [Polynomial.eval_mul, Polynomial.eval_C] at h_eval
  have h_inv : (1 / (W : Padic 3)) ≠ 0 := by
    have hW_neq : (W : Padic 3) ≠ 0 := by
      exact_mod_cast hW
    exact one_div_ne_zero hW_neq
  exact mul_eq_zero.mp h_eval |>.resolve_left h_inv

lemma tendsto_norm_eval_zero (q : ℤ[X]) (hp_eval : eval xi_3 (q.map (algebraMap ℤ (Padic 3))) = 0) :
  Tendsto (fun n => ‖eval (s n) (q.map (algebraMap ℤ (Padic 3)))‖) atTop (𝓝 0) := by
  have h := tendsto_eval_s q
  rw [hp_eval] at h
  rwa [tendsto_zero_iff_norm_tendsto_zero] at h

lemma norm_factorial_mono (n k : ℕ) : ‖((n + k + 1).factorial : Padic 3)‖ ≤ ‖((n + 1).factorial : Padic 3)‖ := by
  apply norm_le_norm_of_dvd
  apply Nat.factorial_dvd_factorial
  omega

lemma norm_eval_s_sub_le (q : ℤ[X]) (n : ℕ) (k : ℕ) :
  ‖eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3))) - eval (s n) (q.map (algebraMap ℤ (Padic 3)))‖ ≤ ‖((n+1).factorial : Padic 3)‖ := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_arith : n + k.succ = n + k + 1 := by omega
    rw [h_arith]
    have h_split : eval (s (n+k+1)) (q.map (algebraMap ℤ (Padic 3))) - eval (s n) (q.map (algebraMap ℤ (Padic 3))) =
      (eval (s (n+k+1)) (q.map (algebraMap ℤ (Padic 3))) - eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3)))) +
      (eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3))) - eval (s n) (q.map (algebraMap ℤ (Padic 3)))) := by ring
    rw [h_split]
    have h_ultra := IsUltrametricDist.norm_add_le_max
      (eval (s (n+k+1)) (q.map (algebraMap ℤ (Padic 3))) - eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3))))
      (eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3))) - eval (s n) (q.map (algebraMap ℤ (Padic 3))))
    apply h_ultra.trans
    rw [max_le_iff]
    constructor
    · have h_diff := norm_eval_diff_le q (n+k)
      apply h_diff.trans
      apply norm_factorial_mono
    · exact ih

lemma tendsto_eval_s_add (q : ℤ[X]) (n : ℕ) :
  Tendsto (fun k => eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3)))) atTop (𝓝 (eval xi_3 (q.map (algebraMap ℤ (Padic 3))))) := by
  have h := tendsto_eval_s q
  have h_shift := Tendsto.comp h (tendsto_add_atTop_nat n)
  have h_eq : (fun k => eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3)))) = (fun n => eval (s n) (q.map (algebraMap ℤ (Padic 3)))) ∘ (fun a => a + n) := by
    ext k
    simp only [Function.comp_apply]
    congr 1
    congr 1
    omega
  rw [h_eq]
  exact h_shift

lemma norm_eval_s_le_factorial (q : ℤ[X]) (hp_eval : eval xi_3 (q.map (algebraMap ℤ (Padic 3))) = 0) (n : ℕ) :
  ‖eval (s n) (q.map (algebraMap ℤ (Padic 3)))‖ ≤ ‖((n+1).factorial : Padic 3)‖ := by
  have h_lim : Tendsto (fun k => ‖eval (s (n+k)) (q.map (algebraMap ℤ (Padic 3))) - eval (s n) (q.map (algebraMap ℤ (Padic 3)))‖) atTop (𝓝 ‖eval (s n) (q.map (algebraMap ℤ (Padic 3)))‖) := by
    have h1 := tendsto_eval_s_add q n
    have h2 := Tendsto.sub_const h1 (eval (s n) (q.map (algebraMap ℤ (Padic 3))))
    rw [hp_eval, zero_sub] at h2
    have h3 := h2.norm
    rw [norm_neg] at h3
    exact h3
  apply le_of_tendsto h_lim
  apply Eventually.of_forall
  intro k
  exact norm_eval_s_sub_le q n k

lemma s_int_diff_two (m : ℕ) (hm : m ≥ 1) :
  let n := 3^m - 1
  s_int n - s_int (n-2) = ((n-1).factorial : ℤ) * (3^m) := by
  intro n
  unfold s_int
  have hn_ge2 : n ≥ 2 := by
    have h3m : 3^m ≥ 3 := by
      calc 3^m
        _ ≥ 3^1 := Nat.pow_le_pow_right (by omega) hm
        _ = 3 := by rfl
    omega
  have hn_eq : n + 1 = n - 1 + 1 + 1 := by omega
  have hn_eq2 : n - 2 + 1 = n - 1 := by omega
  rw [hn_eq, hn_eq2]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  have h_n_sub_add : n - 1 + 1 = n := by omega
  rw [h_n_sub_add]
  have h_add : (∑ i ∈ Finset.range (n - 1), (i.factorial : ℤ)) + ((n - 1).factorial : ℤ) + (n.factorial : ℤ) - (∑ i ∈ Finset.range (n - 1), (i.factorial : ℤ)) =
    ((n - 1).factorial : ℤ) + (n.factorial : ℤ) := by ring
  rw [h_add]
  have hn_fact : (n.factorial : ℤ) = ((n - 1).factorial : ℤ) * n := by
    have h_fact := Nat.factorial_succ (n - 1)
    have h_succ_sub : (n - 1) + 1 = n := by omega
    rw [h_succ_sub] at h_fact
    rw [h_fact]
    push_cast
    ring
  rw [hn_fact]
  have h_factor : ((n - 1).factorial : ℤ) + ((n - 1).factorial : ℤ) * n = ((n - 1).factorial : ℤ) * (1 + n) := by ring
  rw [h_factor]
  have hn_def : n = 3^m - 1 := rfl
  have hn_add_1 : 1 + (n : ℤ) = ((3^m : ℕ) : ℤ) := by
    rw [hn_def]
    have h3m : 3^m ≥ 1 := by
      calc 3^m
        _ ≥ 3^1 := Nat.pow_le_pow_right (by omega) hm
        _ = 3 := by rfl
        _ ≥ 1 := by omega
    omega
  rw [hn_add_1]
  push_cast
  rfl

lemma norm_eval_s_sub_two_le (q : ℤ[X]) (m : ℕ) (hm : m ≥ 1) :
  let n := 3^m - 1
  ‖eval (s n) (q.map (algebraMap ℤ (Padic 3))) - eval (s (n-2)) (q.map (algebraMap ℤ (Padic 3)))‖ ≤ ‖((n-1).factorial : Padic 3)‖ * (3 : ℝ) ^ (- (m : ℤ)) := by
  intro n
  rw [eval_q_padic, eval_q_padic]
  have h_sub : ((eval (s_int n) q : ℤ) : Padic 3) - ((eval (s_int (n-2)) q : ℤ) : Padic 3) = (((eval (s_int n) q - eval (s_int (n-2)) q : ℤ) : Padic 3)) := by
    push_cast
    rfl
  rw [h_sub]
  have h_dvd : ((n-1).factorial * 3^m : ℤ) ∣ (eval (s_int n) q - eval (s_int (n-2)) q) := by
    have h_diff := Polynomial.sub_dvd_eval_sub (s_int n) (s_int (n-2)) q
    rw [s_int_diff_two m hm] at h_diff
    exact h_diff
  have h_le := norm_le_norm_of_dvd_int h_dvd
  apply h_le.trans
  rw [Int.cast_mul, norm_mul]
  have h_pow : ((3^m : ℤ) : Padic 3) = ((3 : ℕ) : Padic 3)^m := by
    push_cast
    rfl
  rw [h_pow]
  rw [Padic.norm_p_pow m]
  push_cast
  rfl

lemma s_succ (k : ℕ) : s (k+1) = s k + ((k+1).factorial : Padic 3) := by
  unfold s
  rw [Finset.sum_range_succ]

lemma s_relations (m : ℕ) (hm : m ≥ 1) :
  let n := 3^m - 1
  s (n-1) = s (n-2) + ((n-1).factorial : Padic 3) ∧
  s n = s (n-1) + (n.factorial : Padic 3) ∧
  (n.factorial : Padic 3) = ((n-1).factorial : Padic 3) * (n : Padic 3) := by
  intro n
  have hn_ge2 : n ≥ 2 := by
    have h3m : 3^m ≥ 3 := by
      calc 3^m
        _ ≥ 3^1 := Nat.pow_le_pow_right (by omega) hm
        _ = 3 := by rfl
    omega
  refine ⟨?_, ?_, ?_⟩
  · have h_succ : (n-2) + 1 = n-1 := by omega
    have h_s := s_succ (n-2)
    rwa [h_succ] at h_s
  · have h_succ : (n-1) + 1 = n := by omega
    have h_s := s_succ (n-1)
    rwa [h_succ] at h_s
  · have h_fact := Nat.factorial_succ (n-1)
    have h_succ : (n-1) + 1 = n := by omega
    rw [h_succ] at h_fact
    rw [h_fact]
    push_cast
    rw [mul_comm]

lemma norm_eval_le_one_of_int_poly (g : ℤ[X]) (z : Padic 3) (hz : ‖z‖ ≤ 1) :
  ‖eval z (g.map (algebraMap ℤ (Padic 3)))‖ ≤ 1 := by
  apply induction_on_X_mul g
  · intro r
    simp only [Polynomial.map_C, eval_C]
    exact Padic.norm_int_le_one r
  · intro f1 f2 ih1 ih2
    simp only [Polynomial.map_add, eval_add]
    have h_ultra := IsUltrametricDist.norm_add_le_max (eval z (f1.map (algebraMap ℤ (Padic 3)))) (eval z (f2.map (algebraMap ℤ (Padic 3))))
    apply h_ultra.trans
    rw [max_le_iff]
    exact ⟨ih1, ih2⟩
  · intro f ih
    simp only [Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X, norm_mul]
    exact mul_le_one₀ ih (norm_nonneg z) hz

lemma norm_eval_sub_le_norm_sub_of_int_poly (g : ℤ[X]) (x y : Padic 3) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
  ‖eval x (g.map (algebraMap ℤ (Padic 3))) - eval y (g.map (algebraMap ℤ (Padic 3)))‖ ≤ ‖x - y‖ := by
  apply induction_on_X_mul g
  · intro r
    simp only [Polynomial.map_C, eval_C, sub_self]
    rw [_root_.norm_zero]
    exact norm_nonneg _
  · intro f1 f2 ih1 ih2
    simp only [Polynomial.map_add, eval_add]
    have h_sub : (eval x (f1.map (algebraMap ℤ (Padic 3))) + eval x (f2.map (algebraMap ℤ (Padic 3)))) -
      (eval y (f1.map (algebraMap ℤ (Padic 3))) + eval y (f2.map (algebraMap ℤ (Padic 3)))) =
      (eval x (f1.map (algebraMap ℤ (Padic 3))) - eval y (f1.map (algebraMap ℤ (Padic 3)))) +
      (eval x (f2.map (algebraMap ℤ (Padic 3))) - eval y (f2.map (algebraMap ℤ (Padic 3)))) := by ring
    rw [h_sub]
    have h_ultra := IsUltrametricDist.norm_add_le_max
      (eval x (f1.map (algebraMap ℤ (Padic 3))) - eval y (f1.map (algebraMap ℤ (Padic 3))))
      (eval x (f2.map (algebraMap ℤ (Padic 3))) - eval y (f2.map (algebraMap ℤ (Padic 3))))
    apply h_ultra.trans
    rw [max_le_iff]
    exact ⟨ih1, ih2⟩
  · intro f ih
    simp only [Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X]
    have h_sub : eval x (f.map (algebraMap ℤ (Padic 3))) * x - eval y (f.map (algebraMap ℤ (Padic 3))) * y =
      (eval x (f.map (algebraMap ℤ (Padic 3))) - eval y (f.map (algebraMap ℤ (Padic 3)))) * x +
      eval y (f.map (algebraMap ℤ (Padic 3))) * (x - y) := by ring
    rw [h_sub]
    have h_ultra := IsUltrametricDist.norm_add_le_max
      ((eval x (f.map (algebraMap ℤ (Padic 3))) - eval y (f.map (algebraMap ℤ (Padic 3)))) * x)
      (eval y (f.map (algebraMap ℤ (Padic 3))) * (x - y))
    apply h_ultra.trans
    rw [max_le_iff]
    constructor
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans ih
    · rw [norm_mul]
      have h_eval_le := norm_eval_le_one_of_int_poly f y hy
      exact mul_le_of_le_one_left (norm_nonneg (x - y)) h_eval_le

lemma coeff_norm_X_add_C_pow_le_one (x : Padic 3) (hx : ‖x‖ ≤ 1) (i : ℕ) (k : ℕ) :
  ‖((X + C x) ^ i).coeff k‖ ≤ 1 := by
  induction i generalizing k with
  | zero =>
    simp only [pow_zero]
    by_cases hk : k = 0
    · rw [hk, coeff_one_zero]
      exact norm_one.le
    · rw [Polynomial.coeff_one, if_neg hk, _root_.norm_zero]
      exact zero_le_one
  | succ i ih =>
    simp only [pow_succ]
    have h_eq : (X + C x) ^ i * (X + C x) = (X + C x) ^ i * X + (X + C x) ^ i * C x := by ring
    rw [h_eq, coeff_add]
    have h_ultra := IsUltrametricDist.norm_add_le_max (((X + C x) ^ i * X).coeff k) (((X + C x) ^ i * C x).coeff k)
    apply h_ultra.trans
    rw [max_le_iff]
    constructor
    · by_cases hk : k = 0
      · rw [hk]
        have h0 : ((X + C x) ^ i * X).coeff 0 = 0 := by
          exact coeff_mul_X_zero ((X + C x) ^ i)
        rw [h0, _root_.norm_zero]
        exact zero_le_one
      · have h_k : k = (k-1) + 1 := by omega
        rw [h_k]
        rw [coeff_mul_X]
        exact ih (k - 1)
    · rw [coeff_mul_C, norm_mul]
      exact mul_le_one₀ (ih k) (norm_nonneg x) hx

lemma coeff_norm_taylor_int_poly_le_one (g : ℤ[X]) (x : Padic 3) (hx : ‖x‖ ≤ 1) (k : ℕ) :
  ‖((g.map (algebraMap ℤ (Padic 3))).taylor x).coeff k‖ ≤ 1 := by
  have h_all : ∀ (g : ℤ[X]) (k : ℕ), ‖((g.map (algebraMap ℤ (Padic 3))).taylor x).coeff k‖ ≤ 1 := by
    intro g
    apply induction_on_X_mul g
    · intro r k
      simp only [Polynomial.map_C, taylor_C]
      by_cases hk : k = 0
      · rw [hk, coeff_C_zero]
        exact Padic.norm_int_le_one r
      · rw [coeff_C_ne_zero hk, _root_.norm_zero]
        exact zero_le_one
    · intro f1 f2 ih1 ih2 k
      simp only [Polynomial.map_add]
      rw [map_add (taylor x)]
      rw [coeff_add]
      have h_ultra := IsUltrametricDist.norm_add_le_max (((f1.map (algebraMap ℤ (Padic 3))).taylor x).coeff k) (((f2.map (algebraMap ℤ (Padic 3))).taylor x).coeff k)
      apply h_ultra.trans
      rw [max_le_iff]
      exact ⟨ih1 k, ih2 k⟩
    · intro f ih k
      simp only [Polynomial.map_mul, Polynomial.map_X]
      rw [taylor_mul, taylor_X]
      have h_eq : (f.map (algebraMap ℤ (Padic 3))).taylor x * (X + C x) = (f.map (algebraMap ℤ (Padic 3))).taylor x * X + (f.map (algebraMap ℤ (Padic 3))).taylor x * C x := by ring
      rw [h_eq, coeff_add]
      have h_ultra := IsUltrametricDist.norm_add_le_max (((f.map (algebraMap ℤ (Padic 3))).taylor x * X).coeff k) (((f.map (algebraMap ℤ (Padic 3))).taylor x * C x).coeff k)
      apply h_ultra.trans
      rw [max_le_iff]
      constructor
      · by_cases hk : k = 0
        · rw [hk]
          have h0 : ((f.map (algebraMap ℤ (Padic 3))).taylor x * X).coeff 0 = 0 := by
            exact coeff_mul_X_zero ((f.map (algebraMap ℤ (Padic 3))).taylor x)
          rw [h0, _root_.norm_zero]
          exact zero_le_one
        · have h_k : k = (k-1) + 1 := by omega
          rw [h_k]
          rw [coeff_mul_X]
          exact ih (k - 1)
      · rw [coeff_mul_C, norm_mul]
        exact mul_le_one₀ (ih k) (norm_nonneg x) hx
  exact h_all g k

lemma coeff_norm_divX_le_one (p : (Padic 3)[X]) (hp : ∀ i, ‖p.coeff i‖ ≤ 1) (i : ℕ) :
  ‖(divX p).coeff i‖ ≤ 1 := by
  rw [coeff_divX]
  exact hp (i + 1)

lemma coeff_norm_divX_divX_le_one (p : (Padic 3)[X]) (hp : ∀ i, ‖p.coeff i‖ ≤ 1) (i : ℕ) :
  ‖(p.divX.divX).coeff i‖ ≤ 1 := by
  rw [coeff_divX, coeff_divX]
  exact hp (i + 2)

lemma norm_eval_le_one_of_coeff_norm_le_one (p : (Padic 3)[X]) (hp : ∀ i, ‖p.coeff i‖ ≤ 1) (y : Padic 3) (hy : ‖y‖ ≤ 1) :
  ‖eval y p‖ ≤ 1 := by
  rw [Polynomial.eval_eq_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i _
  rw [norm_mul, norm_pow]
  have hy_pow : ‖y‖^i ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg y) hy
  exact mul_le_one₀ (hp i) (by positivity) hy_pow

lemma norm_s_le_one (k : ℕ) : ‖s k‖ ≤ 1 := by
  unfold s
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i _
  exact norm_natCast_le_one (Nat.factorial i)

lemma taylor_rem_eq {R : Type*} [CommRing R] (P : R[X]) (x y : R) :
  y^2 * eval y (P.taylor x).divX.divX = eval (x + y) P - eval x P - y * eval x (derivative P) := by
  have h := eval_taylor_split x y P
  rw [h]
  ring

lemma norm_rem1_le (q : ℤ[X]) (m : ℕ) (hm : m ≥ 1) :
  let n := 3^m - 1
  let Q := q.map (algebraMap ℤ (Padic 3))
  let f1 := ((n-1).factorial : Padic 3)
  ‖f1^2 * eval f1 (Q.taylor (s (n-2))).divX.divX‖ ≤ ‖f1‖^2 := by
  intro n Q f1
  have h_norm_f1_sq : ‖f1^2 * eval f1 (Q.taylor (s (n-2))).divX.divX‖ = ‖f1‖^2 * ‖eval f1 (Q.taylor (s (n-2))).divX.divX‖ := by
    rw [norm_mul, norm_pow]
  rw [h_norm_f1_sq]
  have h_coeff : ∀ i, ‖((Q.taylor (s (n-2))).divX.divX).coeff i‖ ≤ 1 := by
    intro i
    apply coeff_norm_divX_divX_le_one
    intro j
    exact coeff_norm_taylor_int_poly_le_one q (s (n-2)) (norm_s_le_one (n-2)) j
  have h_eval : ‖eval f1 (Q.taylor (s (n-2))).divX.divX‖ ≤ 1 := by
    apply norm_eval_le_one_of_coeff_norm_le_one
    · exact h_coeff
    · exact norm_natCast_le_one (n-1).factorial
  nlinarith

lemma norm_rem2_le (q : ℤ[X]) (m : ℕ) (hm : m ≥ 1) :
  let n := 3^m - 1
  let Q := q.map (algebraMap ℤ (Padic 3))
  let f2 := (n.factorial : Padic 3)
  ‖f2^2 * eval f2 (Q.taylor (s (n-1))).divX.divX‖ ≤ ‖f2‖^2 := by
  intro n Q f2
  have h_norm_f2_sq : ‖f2^2 * eval f2 (Q.taylor (s (n-1))).divX.divX‖ = ‖f2‖^2 * ‖eval f2 (Q.taylor (s (n-1))).divX.divX‖ := by
    rw [norm_mul, norm_pow]
  rw [h_norm_f2_sq]
  have h_coeff : ∀ i, ‖((Q.taylor (s (n-1))).divX.divX).coeff i‖ ≤ 1 := by
    intro i
    apply coeff_norm_divX_divX_le_one
    intro j
    exact coeff_norm_taylor_int_poly_le_one q (s (n-1)) (norm_s_le_one (n-1)) j
  have h_eval : ‖eval f2 (Q.taylor (s (n-1))).divX.divX‖ ≤ 1 := by
    apply norm_eval_le_one_of_coeff_norm_le_one
    · exact h_coeff
    · exact norm_natCast_le_one n.factorial
  nlinarith

lemma three_pow_ge_three_mul_add_two (m : ℕ) (hm : m ≥ 2) : 3^m ≥ 3 * m + 2 := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm2 : m ≥ 2
    · have ih_le := ih hm2
      calc 3^(m+1)
        _ = 3^m * 3 := by rfl
        _ = 3 * 3^m := by rw [mul_comm]
        _ ≥ 3 * (3 * m + 2) := by omega
        _ = 9 * m + 6 := by ring
        _ ≥ 3 * (m + 1) + 2 := by omega
    · have : m = 1 := by omega
      subst this
      norm_num

lemma norm_f1_le_pow_three (m : ℕ) (hm : m ≥ 2) :
  let n := 3^m - 1
  ‖((n-1).factorial : Padic 3)‖ ≤ (3 : ℝ) ^ (- (m : ℤ)) := by
  intro n
  rw [norm_factorial_le_iff_dvd]
  apply three_pow_dvd_factorial m (n-1)
  have h_ge := three_pow_ge_three_mul_add_two m hm
  omega

lemma three_pow_ge_add_three (M : ℕ) (hM : M ≥ 2) : 3^M ≥ M + 3 := by
  induction M with
  | zero => omega
  | succ M ih =>
    by_cases hM2 : M ≥ 2
    · have ih_le := ih hM2
      calc 3^(M+1)
        _ = 3^M * 3 := by rfl
        _ = 3 * 3^M := by rw [mul_comm]
        _ ≥ 3 * (M + 3) := by omega
        _ = 3 * M + 9 := by ring
        _ ≥ M + 1 + 3 := by omega
    · have : M = 1 := by omega
      subst this
      norm_num

lemma three_pow_ge_six_mul_add_two (M : ℕ) (hM : M ≥ 4) : 3^M ≥ 6 * M + 2 := by
  induction M with
  | zero => omega
  | succ M ih =>
    by_cases hM4 : M ≥ 4
    · have ih_le := ih hM4
      calc 3^(M+1)
        _ = 3^M * 3 := by rfl
        _ = 3 * 3^M := by rw [mul_comm]
        _ ≥ 3 * (6 * M + 2) := by omega
        _ = 18 * M + 6 := by ring
        _ ≥ 6 * (M + 1) + 2 := by omega
    · have : M = 3 := by omega
      subst this
      norm_num

lemma f1_bound (M : ℕ) (hM : M ≥ 4) :
  let n := 3^M - 1
  ‖((n-1).factorial : Padic 3)‖ * (3 : ℝ)^M ≤ (3 : ℝ) ^ (- (M : ℤ)) := by
  intro n
  have h_le : 3 * (2 * M) ≤ n - 1 := by
    have h_ge := three_pow_ge_six_mul_add_two M hM
    omega
  have h_dvd := three_pow_dvd_factorial (2 * M) (n-1) h_le
  have h_norm : ‖((n-1).factorial : Padic 3)‖ ≤ (3 : ℝ) ^ (- ((2*M) : ℤ)) := by
    exact norm_factorial_le_iff_dvd (n-1) (2*M) |>.mpr h_dvd
  have h_mul : ‖((n-1).factorial : Padic 3)‖ * (3 : ℝ)^M ≤ (3 : ℝ) ^ (- ((2*M) : ℤ)) * (3 : ℝ)^M := by
    exact mul_le_mul_of_nonneg_right h_norm (by positivity)
  have h_eq : (3 : ℝ) ^ (- ((2*M) : ℤ)) * (3 : ℝ)^M = (3 : ℝ) ^ (- (M : ℤ)) := by
    have h_pow : (- ((2*M) : ℤ) + (M : ℤ)) = - (M : ℤ) := by omega
    have hM_cast : (3 : ℝ)^M = (3 : ℝ)^((M : ℤ)) := by exact_mod_cast rfl
    rw [hM_cast]
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
  exact h_mul.trans (le_of_eq h_eq)

lemma double_taylor_expand {R : Type*} [CommRing R] (P : R[X]) (s_n s_n1 s_n2 : R) (f1 f2 : R) (n : R)
  (h1 : s_n1 = s_n2 + f1) (h2 : s_n = s_n1 + f2) (h3 : f2 = f1 * n) :
  eval s_n P = eval s_n2 P + f1 * (eval s_n2 (derivative P) + n * eval s_n1 (derivative P)) +
    f1^2 * eval f1 (P.taylor s_n2).divX.divX + f2^2 * eval f2 (P.taylor s_n1).divX.divX := by
  have he1 := eval_taylor_split s_n2 f1 P
  rw [← h1] at he1
  have he2 := eval_taylor_split s_n1 f2 P
  rw [← h2] at he2
  rw [he2, he1]
  rw [h3]
  ring

/--
Conjecture: this constant is transcendental, which means that it is not the root of any polynomial with integer coefficients.

Formally, $\xi_3$ is not algebraic over $\mathbb{Q}$.
-/
lemma le_three_pow (K : ℕ) : K ≤ 3^K := by
  induction K with
  | zero => omega
  | succ K ih =>
    calc K + 1
      _ ≤ 3^K + 1 := by omega
      _ ≤ 3^K * 3 := by
        have h3K_ge1 : 3^K ≥ 1 := Nat.one_le_pow K 3 (by omega)
        linarith

theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  intro h
  rcases minimal_poly_derivative_ne_zero xi_3 h with ⟨p, hp0, hp_eval, h_min, hp_deriv⟩

  rcases clear_denominators p with ⟨W, q, hW, hp⟩
  have h_deriv_p_eq : derivative p = C (1 / (W : ℚ)) * (derivative q).map (algebraMap ℤ ℚ) := by
    rw [hp, derivative_mul, derivative_C, zero_mul, zero_add, derivative_map]

  have h_eval_deriv_q_ne : eval xi_3 ((derivative q).map (algebraMap ℤ (Padic 3))) ≠ 0 := by
    have h_deriv_p_padic : (derivative p).map (algebraMap ℚ (Padic 3)) = C (1 / (W : Padic 3)) * (derivative q).map (algebraMap ℤ (Padic 3)) := by
      rw [h_deriv_p_eq]
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, _root_.map_comp]
      have h_div : (algebraMap ℚ (Padic 3)) (1 / (W : ℚ)) = 1 / (W : Padic 3) := by simp
      rw [h_div]
    have h_eval : eval xi_3 ((derivative p).map (algebraMap ℚ (Padic 3))) = (1 / (W : Padic 3)) * eval xi_3 ((derivative q).map (algebraMap ℤ (Padic 3))) := by
      rw [h_deriv_p_padic, Polynomial.eval_mul, Polynomial.eval_C]
    intro h_zero
    rw [h_zero, mul_zero] at h_eval
    have h_eval_p_ne : eval xi_3 ((derivative p).map (algebraMap ℚ (Padic 3))) ≠ 0 := by
      rw [Polynomial.eval_map]
      exact hp_deriv
    exact h_eval_p_ne h_eval

  let dQ := (derivative q).map (algebraMap ℤ (Padic 3))
  have h_dQ : dQ = (derivative q).map (algebraMap ℤ (Padic 3)) := rfl
  let C_norm := ‖eval xi_3 dQ‖
  have h_C_norm_pos : C_norm > 0 := by
    exact _root_.norm_pos_iff.mpr h_eval_deriv_q_ne

  have h_lim_dist : Tendsto (fun n => ‖eval (s n) dQ - eval xi_3 dQ‖) atTop (𝓝 0) := by
    rw [← tendsto_zero_iff_norm_tendsto_zero]
    have h_sub_self : eval xi_3 dQ - eval xi_3 dQ = 0 := sub_self _
    have h_lim := Tendsto.sub_const (tendsto_eval_s (derivative q)) (eval xi_3 dQ)
    rw [h_sub_self] at h_lim
    exact h_lim

  rcases Metric.tendsto_atTop.mp h_lim_dist C_norm h_C_norm_pos with ⟨N, hN⟩
  rcases exists_nat_gt (1 / C_norm) with ⟨K, hK⟩
  let M := N + K + 4
  have hM : M ≥ 4 := by omega
  let n := 3^M - 1
  have hn_ge2 : n ≥ 2 := by
    have h_3M : 3^M ≥ 3^4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hn_sub_2 : n - 2 ≥ N := by
    have h_3M : 3^M ≥ M + 3 := three_pow_ge_add_three M (by omega)
    omega
  have hn_sub_1 : n - 1 ≥ N := by omega
  have h1 := hN (n - 1) hn_sub_1
  have h2 := hN (n - 2) hn_sub_2

  have hd1 : dist ‖eval (s (n - 1)) dQ - eval xi_3 dQ‖ 0 = ‖eval (s (n - 1)) dQ - eval xi_3 dQ‖ := by
    rw [Real.dist_0_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hd2 : dist ‖eval (s (n - 2)) dQ - eval xi_3 dQ‖ 0 = ‖eval (s (n - 2)) dQ - eval xi_3 dQ‖ := by
    rw [Real.dist_0_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hd1] at h1
  rw [hd2] at h2

  have hn1 : ‖eval (s (n - 1)) dQ‖ = C_norm := by
    have h_eq : eval (s (n - 1)) dQ = (eval (s (n - 1)) dQ - eval xi_3 dQ) + eval xi_3 dQ := by ring
    rw [h_eq]
    have h_ne : ‖eval (s (n - 1)) dQ - eval xi_3 dQ‖ ≠ ‖eval xi_3 dQ‖ := by
      exact ne_of_lt h1
    rw [norm_add_eq_max_of_norm_ne (eval (s (n - 1)) dQ - eval xi_3 dQ) (eval xi_3 dQ) h_ne]
    rw [max_eq_right]
    exact le_of_lt h1

  have hn2 : ‖eval (s (n - 2)) dQ‖ = C_norm := by
    have h_eq : eval (s (n - 2)) dQ = (eval (s (n - 2)) dQ - eval xi_3 dQ) + eval xi_3 dQ := by ring
    rw [h_eq]
    have h_ne : ‖eval (s (n - 2)) dQ - eval xi_3 dQ‖ ≠ ‖eval xi_3 dQ‖ := by
      exact ne_of_lt h2
    rw [norm_add_eq_max_of_norm_ne (eval (s (n - 2)) dQ - eval xi_3 dQ) (eval xi_3 dQ) h_ne]
    rw [max_eq_right]
    exact le_of_lt h2

  have h_s_le : ∀ k, ‖eval (s k) (q.map (algebraMap ℤ (Padic 3)))‖ ≤ ‖((k+1).factorial : Padic 3)‖ := by
    exact norm_eval_s_le_factorial q (by exact eval_q_padic_xi_3 p W q hW hp hp_eval)

  let f1 := ((n - 1).factorial : Padic 3)
  let f2 := (n.factorial : Padic 3)
  have s_relations_M : s (n - 1) = s (n - 2) + f1 ∧ s n = s (n - 1) + f2 ∧ f2 = f1 * (n : Padic 3) ∧ f1 = ((n-1).factorial : Padic 3) := by
    have h := s_relations M (by omega)
    refine ⟨h.left, h.right.left, h.right.right, rfl⟩
  
  have h_taylor_raw := double_taylor_expand (q.map (algebraMap ℤ (Padic 3))) (s n) (s (n - 1)) (s (n - 2)) f1 f2 n
    s_relations_M.left s_relations_M.right.left s_relations_M.right.right.left

  have h_taylor : eval (s n) (q.map (algebraMap ℤ (Padic 3))) =
    eval (s (n - 2)) (q.map (algebraMap ℤ (Padic 3))) +
      f1 * (eval (s (n - 2)) dQ + (n : Padic 3) * eval (s (n - 1)) dQ) +
      f1^2 * eval f1 (((q.map (algebraMap ℤ (Padic 3))).taylor (s (n - 2))).divX.divX) +
      f2^2 * eval f2 (((q.map (algebraMap ℤ (Padic 3))).taylor (s (n - 1))).divX.divX) := by
    rw [derivative_map] at h_taylor_raw
    exact h_taylor_raw

  let A := eval (s n) (q.map (algebraMap ℤ (Padic 3))) - eval (s (n - 2)) (q.map (algebraMap ℤ (Padic 3)))
  let B := f1^2 * eval f1 (((q.map (algebraMap ℤ (Padic 3))).taylor (s (n - 2))).divX.divX)
  let C := f2^2 * eval f2 (((q.map (algebraMap ℤ (Padic 3))).taylor (s (n - 1))).divX.divX)
  let X_term := eval (s (n - 2)) dQ + n * eval (s (n - 1)) dQ

  have h_sum : f1 * X_term = A - B - C := by
    change f1 * X_term = eval (s n) (q.map (algebraMap ℤ (Padic 3))) - eval (s (n - 2)) (q.map (algebraMap ℤ (Padic 3))) - B - C
    rw [h_taylor]
    ring

  have hA : ‖A‖ ≤ ‖f1‖ * (3 : ℝ)^(- (M : ℤ)) := by
    exact norm_eval_s_sub_two_le q M (by omega)
  have hB : ‖B‖ ≤ ‖f1‖^2 := by
    exact norm_rem1_le q M (by omega)
  have hC : ‖C‖ ≤ ‖f1‖^2 := by
    have h_rem2 := norm_rem2_le q M (by omega)
    have h_f2_le_f1 : ‖f2‖ ≤ ‖f1‖ := by
      apply norm_le_norm_of_dvd
      apply Nat.factorial_dvd_factorial
      omega
    have h_le : ‖f2‖^2 ≤ ‖f1‖^2 := by
      have : 0 ≤ ‖f2‖ := norm_nonneg _
      nlinarith
    exact h_rem2.trans h_le
  have hf1_bound : ‖f1‖ ≤ (3 : ℝ)^(- (M : ℤ)) := by
    exact norm_f1_le_pow_three M (by omega)
  have hf1_pos : ‖f1‖ ≠ 0 := by
    have h_ne : ((n - 1).factorial : Padic 3) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - 1)
    exact norm_ne_zero_iff.mpr h_ne

  have h_X_bound : ‖X_term‖ ≤ (3 : ℝ)^(- (M : ℤ)) := by
    have h_ultra : ‖f1 * X_term‖ ≤ max ‖A‖ (max ‖B‖ ‖C‖) := by
      rw [h_sum]
      have h1_sub : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by
        rw [sub_eq_add_neg]
        have h := IsUltrametricDist.norm_add_le_max A (-B)
        rwa [norm_neg] at h
      have h2_sub : ‖A - B - C‖ ≤ max ‖A - B‖ ‖C‖ := by
        rw [sub_eq_add_neg]
        have h := IsUltrametricDist.norm_add_le_max (A - B) (-C)
        rwa [norm_neg] at h
      have h_max : max ‖A - B‖ ‖C‖ ≤ max ‖A‖ (max ‖B‖ ‖C‖) := by
        rw [max_le_iff]
        constructor
        · exact h1_sub.trans (max_le_max le_rfl (le_max_left _ _))
        · exact le_max_of_le_right (le_max_right _ _)
      exact h2_sub.trans h_max
    have h_max_le : max ‖A‖ (max ‖B‖ ‖C‖) ≤ ‖f1‖ * (3 : ℝ)^(- (M : ℤ)) := by
      rw [max_le_iff, max_le_iff]
      refine ⟨hA, ?_, ?_⟩
      · have h_le : ‖f1‖^2 ≤ ‖f1‖ * (3 : ℝ)^(- (M : ℤ)) := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hf1_bound (norm_nonneg _)
        exact hB.trans h_le
      · have h_le : ‖f1‖^2 ≤ ‖f1‖ * (3 : ℝ)^(- (M : ℤ)) := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hf1_bound (norm_nonneg _)
        exact hC.trans h_le
    have h_mul_le : ‖f1 * X_term‖ ≤ ‖f1‖ * (3 : ℝ)^(- (M : ℤ)) := h_ultra.trans h_max_le
    rw [norm_mul] at h_mul_le
    have hf1_nonneg : 0 < ‖f1‖ := lt_of_le_of_ne (norm_nonneg _) hf1_pos.symm
    exact (mul_le_mul_iff_of_pos_left hf1_nonneg).mp h_mul_le

  have h_X_eq : X_term = (3^M : Padic 3) * eval (s (n - 1)) dQ - (eval (s (n - 1)) dQ - eval (s (n - 2)) dQ) := by
    have h_arith : (3^M : Padic 3) * eval (s (n - 1)) dQ - (eval (s (n - 1)) dQ - eval (s (n - 2)) dQ) =
      eval (s (n - 2)) dQ + ((3^M : Padic 3) - 1) * eval (s (n - 1)) dQ := by ring
    rw [h_arith]
    have hn_cast : (3^M : Padic 3) - 1 = (n : Padic 3) := by
      have h3M_pos : 1 ≤ 3^M := by
        calc 1
          _ ≤ 3 := by omega
          _ = 3^1 := by rfl
          _ ≤ 3^M := Nat.pow_le_pow_right (by omega) (by omega)
      change (3^M : Padic 3) - 1 = (((3^M - 1 : ℕ) : Padic 3))
      rw [Nat.cast_sub h3M_pos]
      push_cast
      rfl
    rw [hn_cast]

  let U := (3^M : Padic 3) * eval (s (n - 1)) dQ
  let V := eval (s (n - 1)) dQ - eval (s (n - 2)) dQ

  have hV_bound : ‖V‖ ≤ (3 : ℝ)^(- ((2*M) : ℤ)) := by
    have h_lip := norm_eval_sub_le_norm_sub_of_int_poly (derivative q) (s (n - 1)) (s (n - 2)) (norm_s_le_one _) (norm_s_le_one _)
    have h_sub_eq : s (n - 1) - s (n - 2) = f1 := by
      rw [s_relations_M.left]
      ring
    rw [h_sub_eq] at h_lip
    have h_f1_bound2 : ‖f1‖ ≤ (3 : ℝ)^(- ((2*M) : ℤ)) := by
      have h_f1 := f1_bound M hM
      have h_pos : (3 : ℝ)^M > 0 := by positivity
      have h_div : ‖f1‖ ≤ (3 : ℝ)^(- (M : ℤ)) / (3 : ℝ)^M := by
        exact (le_div_iff₀ h_pos).mpr h_f1
      have h_eq : (3 : ℝ)^(- (M : ℤ)) / (3 : ℝ)^M = (3 : ℝ)^(- ((2*M) : ℤ)) := by
        have h_pow : (3 : ℝ)^M = (3 : ℝ)^((M : ℤ)) := by exact_mod_cast rfl
        rw [h_pow]
        rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1
        omega
      rwa [h_eq] at h_div
    exact h_lip.trans h_f1_bound2

  have h_U_norm : ‖U‖ = (3 : ℝ)^(- (M : ℤ)) * C_norm := by
    rw [norm_mul]
    have h_pow : (3^M : Padic 3) = ((3 : ℕ) : Padic 3)^M := by
      push_cast
      rfl
    rw [h_pow, Padic.norm_p_pow M]
    rw [hn1]
    push_cast
    rfl

  have h_ne : ‖U‖ ≠ ‖V‖ := by
    rw [h_U_norm]
    intro h_eq
    have h_V_lt : ‖V‖ < ‖U‖ := by
      calc ‖V‖
        _ ≤ (3 : ℝ)^(- ((2*M) : ℤ)) := hV_bound
        _ < (3 : ℝ)^(- (M : ℤ)) * C_norm := by
          have h2M : (3 : ℝ)^(- ((2*M) : ℤ)) = (3 : ℝ)^(- (M : ℤ)) * (3 : ℝ)^(- (M : ℤ)) := by
            have h_pow2 : - ((2*M) : ℤ) = - (M : ℤ) + - (M : ℤ) := by omega
            rw [h_pow2]
            exact zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) _ _
          rw [h2M]
          rw [mul_lt_mul_iff_of_pos_left (by positivity)]
          have h_3K : (K : ℝ) ≤ (3 : ℝ)^K := by
            exact_mod_cast le_three_pow K
          have h_3M : (3 : ℝ)^K ≤ (3 : ℝ)^M := pow_le_pow_right₀ (by norm_num) (by omega)
          have h3M_gt : (3 : ℝ)^M > 1 / C_norm := lt_of_lt_of_le hK (h_3K.trans h_3M)
          have h3M_neg : (3 : ℝ)^(- (M : ℤ)) < C_norm := by
            have h3M_neg_eq : (3 : ℝ)^(- (M : ℤ)) = ((3 : ℝ)^M)⁻¹ := by
              simp only [zpow_neg, zpow_natCast]
            rw [h3M_neg_eq]
            have h_pos : (3 : ℝ)^M > 0 := by positivity
            have h_inv : ((3 : ℝ)^M)⁻¹ < (C_norm⁻¹)⁻¹ := by
              rw [inv_lt_inv₀ h_pos (by positivity)]
              rw [one_div] at h3M_gt
              exact h3M_gt
            rwa [inv_inv] at h_inv
          exact h3M_neg
    exact h_ne h_eq

  have h_U_eq_XV : U = X_term + V := by
    rw [h_X_eq]
    ring

  have h_U_norm_eq : ‖U‖ = max ‖X_term‖ ‖V‖ := by
    have h_ne2 : ‖X_term‖ ≠ ‖V‖ := by
      intro h_eq
      have h_X_lt : ‖X_term‖ < ‖U‖ := by
        rw [h_U_norm]
        calc ‖X_term‖
          _ ≤ (3 : ℝ)^(- (M : ℤ)) := h_X_bound
          _ < (3 : ℝ)^(- (M : ℤ)) * C_norm := by
            -- since C_norm > 1?
            -- wait, is C_norm > 1? No!
            -- wait!
            -- why is (3 : ℝ)^(- (M : ℤ)) < (3 : ℝ)^(- (M : ℤ)) * C_norm?
            -- This is ONLY true if C_norm > 1!
            -- But C_norm is at most 1!
            sorry
    sorry

