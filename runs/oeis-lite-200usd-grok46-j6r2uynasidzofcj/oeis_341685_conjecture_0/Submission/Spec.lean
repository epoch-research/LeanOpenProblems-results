import FormalConjectures.Util.ProblemImports

open Nat BigOperators Filter Topology

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

/--
The 3-adic constant $\xi_3 = \sum_{k \ge 0} k!$.
This series converges in `Padic 3`.
-/
noncomputable def xi_3 : Padic 3 :=
  tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

open Algebra

/-! ### Summability of `∑ k!` in `ℚ_[3]` -/

lemma padicValNat_factorial_ge_div (n : ℕ) :
    n / 3 ≤ padicValNat 3 n.factorial := by
  have hsum := padicValNat_factorial (p := 3) (n := n) (b := n + 2) (by
    have : Nat.log 3 n ≤ n := Nat.log_le_self 3 n
    omega)
  have hmem : 1 ∈ Finset.Ico 1 (n + 2) := by
    simp [Finset.mem_Ico]
  have : n / (3 ^ 1) ≤ ∑ i ∈ Finset.Ico 1 (n + 2), n / 3 ^ i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (n / 3 ^ i)) hmem
  calc
    n / 3 = n / (3 ^ 1) := by simp
    _ ≤ ∑ i ∈ Finset.Ico 1 (n + 2), n / 3 ^ i := this
    _ = padicValNat 3 n.factorial := hsum.symm

lemma tendsto_padicValNat_factorial :
    Tendsto (fun n : ℕ => padicValNat 3 n.factorial) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun B => ⟨3 * B + 3, fun n hn => ?_⟩
  have : n / 3 ≤ padicValNat 3 n.factorial := padicValNat_factorial_ge_div n
  omega

lemma norm_factorial_padic (k : ℕ) :
    ‖(k.factorial : Padic 3)‖ = (3 : ℝ) ^ (-(padicValNat 3 k.factorial : ℤ)) := by
  have hne : (k.factorial : Padic 3) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
  simp

lemma tendsto_inv_three_pow_zero :
    Tendsto (fun n : ℕ => ((3 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma tendsto_factorial_padic_zero :
    Tendsto (fun k : ℕ => (k.factorial : Padic 3)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 tendsto_inv_three_pow_zero) ε hε
  obtain ⟨N2, hN2⟩ := tendsto_atTop_atTop.1 tendsto_padicValNat_factorial N1
  refine ⟨N2, fun n hn => ?_⟩
  have hval : N1 ≤ padicValNat 3 n.factorial := hN2 n hn
  have hnorm : ‖(n.factorial : Padic 3)‖ = ((3 : ℝ)⁻¹) ^ (padicValNat 3 n.factorial) := by
    rw [norm_factorial_padic, zpow_neg, zpow_natCast, inv_pow]
  have hle : ((3 : ℝ)⁻¹) ^ (padicValNat 3 n.factorial) ≤ ((3 : ℝ)⁻¹) ^ N1 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hval
  have hlt : Dist.dist (((3 : ℝ)⁻¹) ^ N1) 0 < ε := hN1 N1 le_rfl
  have : ‖(n.factorial : Padic 3)‖ < ε := by
    rw [hnorm]
    have : Dist.dist (((3 : ℝ)⁻¹) ^ N1) 0 = |((3 : ℝ)⁻¹) ^ N1| := by
      simp [Dist.dist]
    rw [this] at hlt
    have hnn : 0 ≤ ((3 : ℝ)⁻¹) ^ N1 := by positivity
    rw [abs_of_nonneg hnn] at hlt
    exact lt_of_le_of_lt hle hlt
  simpa [Dist.dist, dist_eq_norm] using this

lemma summable_factorial_padic :
    Summable (fun k : ℕ => (k.factorial : Padic 3)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  exact tendsto_factorial_padic_zero

lemma xi_3_hasSum :
    HasSum (fun k : ℕ => (k.factorial : Padic 3)) xi_3 := by
  simpa [xi_3] using summable_factorial_padic.hasSum

lemma tendsto_partialSum_xi_3 :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (k.factorial : Padic 3)) atTop (nhds xi_3) :=
  xi_3_hasSum.tendsto_sum_nat

lemma xi_3_eq_sum_add_tail (n : ℕ) :
    xi_3 = ∑ k ∈ Finset.range n, (k.factorial : Padic 3) +
      ∑' k : ℕ, ((k + n).factorial : Padic 3) := by
  simpa using (summable_factorial_padic.sum_add_tsum_nat_add n).symm

lemma norm_factorial_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    ‖(k.factorial : Padic 3)‖ ≤ (3 : ℝ)⁻¹ := by
  have hdiv : 3 ∣ k.factorial := by
    exact Nat.dvd_factorial (by norm_num) hk
  have : 1 ≤ padicValNat 3 k.factorial :=
    one_le_padicValNat_of_dvd (Nat.factorial_ne_zero k) hdiv
  rw [norm_factorial_padic]
  have : (3 : ℝ) ^ (-(padicValNat 3 k.factorial : ℤ)) ≤ (3 : ℝ) ^ (-(1 : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    exact Int.neg_le_neg (by exact_mod_cast this)
  simpa [zpow_neg, zpow_one] using this

lemma xi_3_sub_one_norm : ‖xi_3 - 1‖ < 1 := by
  -- ξ - 1 = 1! + 2! + ∑_{k≥3} k! = 3 + ∑_{k≥3} k!
  have hdecomp : xi_3 - 1 =
      (3 : Padic 3) + ∑' k : ℕ, ((k + 3).factorial : Padic 3) := by
    have h := xi_3_eq_sum_add_tail 3
    have hrange : ∑ k ∈ Finset.range 3, (k.factorial : Padic 3) = 4 := by
      simp [Finset.sum_range_succ, Nat.factorial_succ]
      norm_num
    have : (4 : Padic 3) = 1 + 3 := by norm_num
    rw [hrange, this] at h
    linear_combination h
  rw [hdecomp]
  have h3 : ‖(3 : Padic 3)‖ = (3 : ℝ)⁻¹ := Padic.norm_p
  have htail : ‖∑' k : ℕ, ((k + 3).factorial : Padic 3)‖ ≤ (3 : ℝ)⁻¹ := by
    -- each term has norm ≤ 1/3, so the tsum does too (ultrametric)
    have hsm : Summable (fun k : ℕ => ((k + 3).factorial : Padic 3)) := by
      simpa using (summable_nat_add_iff (f := fun k => (k.factorial : Padic 3)) 3).2
        summable_factorial_padic
    -- Use that terms tend to 0 and each has norm ≤ 1/3
    have hle : ∀ k, ‖((k + 3).factorial : Padic 3)‖ ≤ (3 : ℝ)⁻¹ :=
      fun k => norm_factorial_of_three_le (by omega)
    -- nonarchimedean: ‖tsum‖ ≤ ⨆ ‖term‖ ≤ 1/3
    refine le_trans ?_ (le_of_eq rfl)
    -- fallback: ‖tsum‖ = lim ‖partial‖ ≤ 1/3
    have hpart : ∀ N, ‖∑ k ∈ Finset.range N, ((k + 3).factorial : Padic 3)‖ ≤ (3 : ℝ)⁻¹ := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (hle N))
    have ht := hsm.hasSum.tendsto_sum_nat
    have : Tendsto (fun N => ‖∑ k ∈ Finset.range N, ((k + 3).factorial : Padic 3)‖)
        atTop (nhds ‖∑' k : ℕ, ((k + 3).factorial : Padic 3)‖) :=
      (continuous_norm.tendsto _).comp ht
    exact le_of_tendsto_of_tendsto this tendsto_const_nhds
      (Eventually.of_forall hpart)
  have : ‖(3 : Padic 3) + ∑' k : ℕ, ((k + 3).factorial : Padic 3)‖ ≤ (3 : ℝ)⁻¹ :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (le_of_eq h3) htail)
  exact lt_of_le_of_lt this (by norm_num)

lemma xi_3_ne_zero : xi_3 ≠ 0 := by
  intro h
  have := xi_3_sub_one_norm
  rw [h, zero_sub, norm_neg] at this
  have : ‖(1 : Padic 3)‖ = 1 := by simp
  linarith

lemma norm_factorial_le_one (k : ℕ) :
    ‖(k.factorial : Padic 3)‖ ≤ 1 := by
  rw [norm_factorial_padic]
  have : (3 : ℝ) ^ (-(padicValNat 3 k.factorial : ℤ)) ≤ (3 : ℝ) ^ (0 : ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  simpa using this

lemma xi_3_norm_le_one : ‖xi_3‖ ≤ 1 := by
  have hpart : ∀ N, ‖∑ k ∈ Finset.range N, (k.factorial : Padic 3)‖ ≤ 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ih (norm_factorial_le_one N))
  have ht := tendsto_partialSum_xi_3
  have : Tendsto (fun N => ‖∑ k ∈ Finset.range N, (k.factorial : Padic 3)‖)
      atTop (nhds ‖xi_3‖) :=
    (continuous_norm.tendsto _).comp ht
  exact le_of_tendsto_of_tendsto this tendsto_const_nhds (Eventually.of_forall hpart)

lemma padicValNat_factorial_le_add (n k : ℕ) :
    padicValNat 3 n.factorial ≤ padicValNat 3 (k + n).factorial := by
  have hdiv : n.factorial ∣ (k + n).factorial :=
    Nat.factorial_dvd_factorial (Nat.le_add_left n k)
  have hpow : 3 ^ padicValNat 3 n.factorial ∣ (k + n).factorial :=
    dvd_trans pow_padicValNat_dvd hdiv
  exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero (k + n))).1 hpow

lemma norm_factorial_anti (n k : ℕ) :
    ‖((k + n).factorial : Padic 3)‖ ≤ ‖(n.factorial : Padic 3)‖ := by
  rw [norm_factorial_padic, norm_factorial_padic]
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  exact Int.neg_le_neg (by exact_mod_cast padicValNat_factorial_le_add n k)

lemma tail_norm_le (n : ℕ) :
    ‖∑' k : ℕ, ((k + n).factorial : Padic 3)‖ ≤ ‖(n.factorial : Padic 3)‖ := by
  have hsm : Summable (fun k : ℕ => ((k + n).factorial : Padic 3)) := by
    simpa using (summable_nat_add_iff (f := fun k => (k.factorial : Padic 3)) n).2
      summable_factorial_padic
  have hpart : ∀ N,
      ‖∑ k ∈ Finset.range N, ((k + n).factorial : Padic 3)‖ ≤ ‖(n.factorial : Padic 3)‖ := by
    intro N
    induction N with
    | zero =>
      simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ih (norm_factorial_anti n N))
  have ht := hsm.hasSum.tendsto_sum_nat
  have : Tendsto (fun N => ‖∑ k ∈ Finset.range N, ((k + n).factorial : Padic 3)‖)
      atTop (nhds ‖∑' k : ℕ, ((k + n).factorial : Padic 3)‖) :=
    (continuous_norm.tendsto _).comp ht
  exact le_of_tendsto_of_tendsto this tendsto_const_nhds (Eventually.of_forall hpart)

/-- Partial sum `S n = ∑_{k < n} k!`. -/
noncomputable def S (n : ℕ) : Padic 3 :=
  ∑ k ∈ Finset.range n, (k.factorial : Padic 3)

lemma xi_3_eq_S_add_tail (n : ℕ) :
    xi_3 = S n + ∑' k : ℕ, ((k + n).factorial : Padic 3) :=
  xi_3_eq_sum_add_tail n

/-- `T n = (ξ - S n) / n!`, a 3-adic integer interpolating `∑_{k≥0} (n+1)⋯(n+k)`. -/
noncomputable def T (n : ℕ) : Padic 3 :=
  (xi_3 - S n) / (n.factorial : Padic 3)

lemma factorial_ne_zero_padic (n : ℕ) : (n.factorial : Padic 3) ≠ 0 :=
  by exact_mod_cast Nat.factorial_ne_zero n

lemma T_mul_factorial (n : ℕ) :
    T n * (n.factorial : Padic 3) = xi_3 - S n := by
  rw [T, div_mul_cancel₀ _ (factorial_ne_zero_padic n)]

lemma xi_3_eq_S_add_T (n : ℕ) :
    xi_3 = S n + (n.factorial : Padic 3) * T n := by
  linear_combination (T_mul_factorial n).symm

lemma T_norm_le_one (n : ℕ) : ‖T n‖ ≤ 1 := by
  have hdiv : xi_3 - S n = ∑' k : ℕ, ((k + n).factorial : Padic 3) := by
    linear_combination (xi_3_eq_S_add_tail n)
  have hle := tail_norm_le n
  have hne := factorial_ne_zero_padic n
  have : ‖T n‖ = ‖xi_3 - S n‖ / ‖(n.factorial : Padic 3)‖ := by
    rw [T, norm_div]
  rw [this, hdiv]
  have hpos : 0 < ‖(n.factorial : Padic 3)‖ := norm_pos_iff.mpr hne
  exact (div_le_one hpos).mpr hle

lemma T_succ (n : ℕ) : T n = 1 + ((n + 1 : ℕ) : Padic 3) * T (n + 1) := by
  -- T n = (ξ - S n)/n! and S (n+1) = S n + n!, so
  -- ξ - S n = n! + (ξ - S (n+1)) = n! + (n+1)! T (n+1)
  -- hence T n = 1 + (n+1) T (n+1)
  have hS : S (n + 1) = S n + (n.factorial : Padic 3) := by
    simp [S, Finset.sum_range_succ]
  have hfac : ((n + 1).factorial : Padic 3) =
      ((n + 1 : ℕ) : Padic 3) * (n.factorial : Padic 3) := by
    rw [Nat.factorial_succ]
    exact_mod_cast rfl
  have h1 : xi_3 - S n = (n.factorial : Padic 3) + (xi_3 - S (n + 1)) := by
    rw [hS]; ring
  have h2 : xi_3 - S (n + 1) = ((n + 1).factorial : Padic 3) * T (n + 1) := by
    linear_combination (T_mul_factorial (n + 1)).symm
  have hne := factorial_ne_zero_padic n
  apply mul_right_cancel₀ hne
  calc
    T n * (n.factorial : Padic 3) = xi_3 - S n := T_mul_factorial n
    _ = (n.factorial : Padic 3) + ((n + 1).factorial : Padic 3) * T (n + 1) := by
      rw [h1, h2]
    _ = (n.factorial : Padic 3) +
          (((n + 1 : ℕ) : Padic 3) * (n.factorial : Padic 3)) * T (n + 1) := by
      rw [hfac]
    _ = (1 + ((n + 1 : ℕ) : Padic 3) * T (n + 1)) * (n.factorial : Padic 3) := by
      ring

lemma natCast_padic_norm_le_inv_three {m : ℕ} (hm : 3 ∣ m) :
    ‖((m : ℕ) : Padic 3)‖ ≤ (3 : ℝ)⁻¹ := by
  rcases eq_or_ne m 0 with rfl | hne
  · simp
  have hval : 1 ≤ padicValNat 3 m := one_le_padicValNat_of_dvd hne hm
  have hne' : ((m : ℕ) : Padic 3) ≠ 0 := by exact_mod_cast hne
  rw [Padic.norm_eq_zpow_neg_valuation hne', Padic.valuation_natCast]
  have : (3 : ℝ) ^ (-(padicValNat 3 m : ℤ)) ≤ (3 : ℝ) ^ (-(1 : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    exact Int.neg_le_neg (by exact_mod_cast hval)
  simpa [zpow_neg, zpow_one] using this

lemma T_mod_three_of_two {n : ℕ} (hn : n % 3 = 2) :
    ‖T n - 1‖ ≤ (3 : ℝ)⁻¹ := by
  have hsucc : 3 ∣ n + 1 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hnorm : ‖((n + 1 : ℕ) : Padic 3)‖ ≤ (3 : ℝ)⁻¹ :=
    natCast_padic_norm_le_inv_three hsucc
  have hdiff : T n - 1 = ((n + 1 : ℕ) : Padic 3) * T (n + 1) := by
    rw [T_succ]; ring
  rw [hdiff, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) (T_norm_le_one (n + 1)) |>.trans ?_
  simpa using hnorm

lemma padic_norm_eq_of_norm_sub_lt {x y : Padic 3} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have hx : ‖x‖ ≤ ‖y‖ := by
    have : x = (x - y) + y := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max (x - y) y).trans (max_le (le_of_lt h) le_rfl)
  have hy : ‖y‖ ≤ ‖x‖ := by
    have hle : ‖y‖ ≤ max ‖x‖ ‖x - y‖ := by
      calc
        ‖y‖ = ‖x + -(x - y)‖ := by congr 1; ring
        _ ≤ max ‖x‖ ‖-(x - y)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖x‖ ‖x - y‖ := by rw [norm_neg]
    rcases le_total ‖x‖ ‖x - y‖ with h' | h'
    · exact absurd ((max_eq_right h').subst hle) h.not_ge
    · exact (max_eq_left h').subst hle
  exact le_antisymm hx hy

lemma T_unit_of_two {n : ℕ} (hn : n % 3 = 2) : ‖T n‖ = 1 := by
  have hlt : ‖T n - 1‖ < 1 :=
    lt_of_le_of_lt (T_mod_three_of_two hn) (by norm_num)
  simpa using padic_norm_eq_of_norm_sub_lt (x := T n) (y := 1) (by simpa using hlt)

lemma xi_3_sub_S_norm_eq {n : ℕ} (hn : n % 3 = 2) :
    ‖xi_3 - S n‖ = ‖(n.factorial : Padic 3)‖ := by
  have h := xi_3_eq_S_add_T n
  have : xi_3 - S n = (n.factorial : Padic 3) * T n := by linear_combination h
  rw [this, norm_mul, T_unit_of_two hn, mul_one]

lemma xi_3_norm_eq_one : ‖xi_3‖ = 1 := by
  simpa using padic_norm_eq_of_norm_sub_lt (x := xi_3) (y := 1) (by simpa using xi_3_sub_one_norm)

lemma three_dvd_of_three_consecutive (m : ℕ) :
    3 ∣ (m + 1) ∨ 3 ∣ (m + 2) ∨ 3 ∣ (m + 3) := by
  have : (m + 1) % 3 = 0 ∨ (m + 2) % 3 = 0 ∨ (m + 3) % 3 = 0 := by omega
  simpa [Nat.dvd_iff_mod_eq_zero] using this

lemma padicValNat_mul_three_consecutive (m : ℕ) :
    1 ≤ padicValNat 3 ((m + 1) * (m + 2) * (m + 3)) := by
  have h3 : 3 ∣ (m + 1) * (m + 2) * (m + 3) := by
    rcases three_dvd_of_three_consecutive m with h | h | h
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
    · exact dvd_mul_of_dvd_right h _
  exact one_le_padicValNat_of_dvd (by positivity) h3

lemma factorial_add_three (m : ℕ) :
    (m + 3).factorial = (m + 1) * (m + 2) * (m + 3) * m.factorial := by
  simp [Nat.factorial_succ]
  ring

lemma padicValNat_factorial_add_three (m : ℕ) :
    padicValNat 3 m.factorial < padicValNat 3 (m + 3).factorial := by
  have hne1 : (m + 1 : ℕ) ≠ 0 := by omega
  have hne2 : (m + 2 : ℕ) ≠ 0 := by omega
  have hne3 : (m + 3 : ℕ) ≠ 0 := by omega
  have hnef : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hsum : padicValNat 3 (m + 3).factorial =
      padicValNat 3 ((m + 1) * (m + 2) * (m + 3)) + padicValNat 3 m.factorial := by
    rw [factorial_add_three, padicValNat.mul (mul_ne_zero (mul_ne_zero hne1 hne2) hne3) hnef]
  have := padicValNat_mul_three_consecutive m
  omega


lemma T_eq_two_terms (m : ℕ) :
    T m = 1 + ((m + 1 : ℕ) : Padic 3) +
      ((m + 1 : ℕ) : Padic 3) * ((m + 2 : ℕ) : Padic 3) * T (m + 2) := by
  rw [T_succ m, T_succ (m + 1)]
  ring

lemma T_mod_three_of_zero {n : ℕ} (hn : n % 3 = 0) :
    ‖T n - 1‖ ≤ (3 : ℝ)⁻¹ := by
  -- T n = 1+(n+1)+(n+1)(n+2)T(n+2), n≡0 ⇒ n+1≡1, n+2≡2
  -- and T(n+2)≡1 (mod 3) since n+2≡2, so the display is
  -- 1 + 1 + (1)(2)(1) ≡ 1 (mod 3)
  have h2 : (n + 2) % 3 = 2 := by omega
  have hT2 : ‖T (n + 2) - 1‖ ≤ (3 : ℝ)⁻¹ := T_mod_three_of_two h2
  have hn1 : ¬ (3 ∣ n + 1) := by
    intro h
    have : (n + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  have hn2unit : ¬ (3 ∣ n + 2) := by
    intro h
    have : (n + 2) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  have hnorm1 : ‖((n + 1 : ℕ) : Padic 3)‖ = 1 := by
    have hne : ((n + 1 : ℕ) : Padic 3) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
    have : padicValNat 3 (n + 1) = 0 :=
      (padicValNat.eq_zero_iff).2 (Or.inr (Or.inr hn1))
    simp [this]
  have hnorm2 : ‖((n + 2 : ℕ) : Padic 3)‖ = 1 := by
    have hne : ((n + 2 : ℕ) : Padic 3) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
    have : padicValNat 3 (n + 2) = 0 :=
      (padicValNat.eq_zero_iff).2 (Or.inr (Or.inr hn2unit))
    simp [this]
  -- T n - 1 = (n+1) + (n+1)(n+2) T(n+2)
  --         = (n+1) (1 + (n+2) T(n+2))
  --         = (n+1) T(n+1)
  -- and T(n+1) - (n+2)? use two-term form vs 1:
  -- T n - 1 = (n+1) [1 + (n+2) T(n+2)] + 0 wait
  -- From T_eq_two_terms: T n - 1 = (n+1) + (n+1)(n+2)T(n+2)
  -- Compare with (n+1)+(n+1)(n+2) = (n+1)(n+3):
  -- T n - 1 - (n+1)(1+(n+2)) = (n+1)(n+2)(T(n+2)-1)
  have hdiff :
      T n - 1 - ((n + 1 : ℕ) : Padic 3) * (1 + ((n + 2 : ℕ) : Padic 3)) =
        ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * (T (n + 2) - 1) := by
    rw [T_eq_two_terms]; ring
  have hmain :
      ‖((n + 1 : ℕ) : Padic 3) * (1 + ((n + 2 : ℕ) : Padic 3))‖ ≤ (3 : ℝ)⁻¹ := by
    -- n+1 + (n+1)(n+2) = (n+1)(n+3) and n+3 ≡ 0 (mod 3)
    have hdiv : 3 ∣ n + 3 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have :
        ((n + 1 : ℕ) : Padic 3) * (1 + ((n + 2 : ℕ) : Padic 3)) =
          ((n + 1 : ℕ) : Padic 3) * ((n + 3 : ℕ) : Padic 3) := by
      push_cast; ring
    rw [this, norm_mul, hnorm1, one_mul]
    exact natCast_padic_norm_le_inv_three hdiv
  have hrest :
      ‖((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * (T (n + 2) - 1)‖ ≤
        (3 : ℝ)⁻¹ := by
    rw [norm_mul, norm_mul, hnorm1, hnorm2, one_mul, one_mul]
    exact hT2
  have : T n - 1 =
      ((n + 1 : ℕ) : Padic 3) * (1 + ((n + 2 : ℕ) : Padic 3)) +
        ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * (T (n + 2) - 1) := by
    linear_combination hdiff
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hmain hrest)

lemma T_unit_of_zero {n : ℕ} (hn : n % 3 = 0) : ‖T n‖ = 1 := by
  have hlt : ‖T n - 1‖ < 1 :=
    lt_of_le_of_lt (T_mod_three_of_zero hn) (by norm_num)
  simpa using padic_norm_eq_of_norm_sub_lt (x := T n) (y := 1) (by simpa using hlt)

lemma T_ne_zero_of_zero {n : ℕ} (hn : n % 3 = 0) : T n ≠ 0 := by
  intro h
  have := T_unit_of_zero hn
  rw [h, _root_.norm_zero] at this
  norm_num at this

lemma T_ne_zero_of_two {n : ℕ} (hn : n % 3 = 2) : T n ≠ 0 := by
  intro h
  have := T_unit_of_two hn
  rw [h, _root_.norm_zero] at this
  norm_num at this

lemma xi_3_ne_S_of_two {n : ℕ} (hn : n % 3 = 2) : xi_3 ≠ S n := by
  intro h
  have hT : T n = 0 := by
    have hmul := T_mul_factorial n
    rw [h, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (factorial_ne_zero_padic n)
  exact T_ne_zero_of_two hn hT

/-- `S 9 = 46234`. -/
lemma S_nine : S 9 = ((46234 : ℕ) : Padic 3) := by
  simp [S, Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

lemma padicValNat_nine_factorial : padicValNat 3 (9 : ℕ).factorial = 4 := by
  native_decide

lemma padicValNat_S_nine_sub_one : padicValNat 3 (46233 : ℕ) = 2 := by
  native_decide

lemma xi_3_sub_one_eq_S_nine_sub_one_add_tail :
    xi_3 - 1 = ((46233 : ℕ) : Padic 3) + ((9 : ℕ).factorial : Padic 3) * T 9 := by
  have h := xi_3_eq_S_add_T 9
  have hS := S_nine
  have hnum : ((46234 : ℕ) : Padic 3) - 1 = ((46233 : ℕ) : Padic 3) := by
    norm_cast
  rw [h, hS]
  linear_combination hnum

lemma norm_nine_factorial :
    ‖((9 : ℕ).factorial : Padic 3)‖ = (3 : ℝ) ^ (-(4 : ℤ)) := by
  rw [norm_factorial_padic, padicValNat_nine_factorial]
  simp

lemma xi_3_sub_one_valuation_eq_two : ‖xi_3 - 1‖ = (3 : ℝ) ^ (-(2 : ℤ)) := by
  have hdecomp := xi_3_sub_one_eq_S_nine_sub_one_add_tail
  have hne : ((46233 : ℕ) : Padic 3) ≠ 0 := by
    exact_mod_cast (by norm_num : (46233 : ℕ) ≠ 0)
  have hSnorm : ‖((46233 : ℕ) : Padic 3)‖ = (3 : ℝ) ^ (-(2 : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast,
      padicValNat_S_nine_sub_one]
    simp
  have htail : ‖((9 : ℕ).factorial : Padic 3) * T 9‖ < ‖((46233 : ℕ) : Padic 3)‖ := by
    rw [norm_mul, norm_nine_factorial, hSnorm]
    have hT : ‖T 9‖ ≤ 1 := T_norm_le_one 9
    have : (3 : ℝ) ^ (-(4 : ℤ)) * ‖T 9‖ ≤ (3 : ℝ) ^ (-(4 : ℤ)) :=
      mul_le_of_le_one_right (zpow_nonneg (by norm_num) _) hT
    refine lt_of_le_of_lt this ?_
    apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 3)
    norm_num
  have : ‖xi_3 - 1‖ = ‖((46233 : ℕ) : Padic 3)‖ := by
    rw [hdecomp]
    exact padic_norm_eq_of_norm_sub_lt
      (x := ((46233 : ℕ) : Padic 3) + ((9 : ℕ).factorial : Padic 3) * T 9)
      (y := ((46233 : ℕ) : Padic 3)) (by simpa [add_sub_cancel_left] using htail)
  rw [this, hSnorm]

lemma T_mod_three_of_one {n : ℕ} (hn : n % 3 = 1) :
    ‖T n‖ ≤ (3 : ℝ)⁻¹ := by
  have h2 : (n + 1) % 3 = 2 := by omega
  have hT : ‖T (n + 1) - 1‖ ≤ (3 : ℝ)⁻¹ := T_mod_three_of_two h2
  have hn1 : 3 ∣ n + 1 ∨ ¬ 3 ∣ n + 1 := em _
  -- n ≡ 1 ⇒ n+1 ≡ 2, so 3 ∤ n+1
  have hndiv : ¬ 3 ∣ n + 1 := by
    intro h
    have : (n + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  have hnorm : ‖((n + 1 : ℕ) : Padic 3)‖ = 1 := by
    have hne : ((n + 1 : ℕ) : Padic 3) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
    have : padicValNat 3 (n + 1) = 0 :=
      (padicValNat.eq_zero_iff).2 (Or.inr (Or.inr hndiv))
    simp [this]
  -- T n = 1 + (n+1) T(n+1) = 1 + (n+1) + (n+1)(T(n+1)-1)
  -- 1+(n+1) = n+2 ≡ 0 (mod 3)
  have hdiv2 : 3 ∣ n + 2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hmain : ‖((n + 2 : ℕ) : Padic 3)‖ ≤ (3 : ℝ)⁻¹ :=
    natCast_padic_norm_le_inv_three hdiv2
  have hrest :
      ‖((n + 1 : ℕ) : Padic 3) * (T (n + 1) - 1)‖ ≤ (3 : ℝ)⁻¹ := by
    rw [norm_mul, hnorm, one_mul]
    exact hT
  have hdecomp :
      T n = ((n + 2 : ℕ) : Padic 3) +
        ((n + 1 : ℕ) : Padic 3) * (T (n + 1) - 1) := by
    have : ((n + 2 : ℕ) : Padic 3) = (1 : Padic 3) + ((n + 1 : ℕ) : Padic 3) := by
      push_cast; ring
    rw [T_succ, this]
    ring
  rw [hdecomp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hmain hrest)

/-- The three residue classes of `T` on `ℕ`. -/
lemma T_norm_cases (n : ℕ) :
    (n % 3 = 0 ∧ ‖T n‖ = 1) ∨
    (n % 3 = 1 ∧ ‖T n‖ ≤ (3 : ℝ)⁻¹) ∨
    (n % 3 = 2 ∧ ‖T n‖ = 1) := by
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h
  · exact Or.inl ⟨h, T_unit_of_zero h⟩
  · exact Or.inr (Or.inl ⟨h, T_mod_three_of_one h⟩)
  · exact Or.inr (Or.inr ⟨h, T_unit_of_two h⟩)

/-- Integer value of the partial sum. -/
def Snat (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, k.factorial

lemma S_eq_natCast (n : ℕ) : S n = ((Snat n : ℕ) : Padic 3) := by
  simp [S, Snat]

lemma Snat_succ (n : ℕ) : Snat (n + 1) = Snat n + n.factorial := by
  simp [Snat, Finset.sum_range_succ]

lemma Snat_mono {m n : ℕ} (h : m ≤ n) : Snat m ≤ Snat n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)

lemma Snat_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Snat n := by
  have : Snat 1 ≤ Snat n := Snat_mono hn
  simpa [Snat] using this

/-- Three-step increment of the partial-sum sequence. -/
lemma Snat_add_three (n : ℕ) :
    Snat (n + 3) = Snat n + n.factorial * (n + 2) ^ 2 := by
  have hsum :
      n.factorial + (n + 1).factorial + (n + 2).factorial =
        n.factorial * (n + 2) ^ 2 := by
    simp [Nat.factorial_succ]
    ring
  simp [Snat, Finset.sum_range_succ]
  linear_combination hsum

lemma S_add_three (n : ℕ) :
    S (n + 3) = S n + (n.factorial : Padic 3) * (((n + 2 : ℕ) : Padic 3) ^ 2) := by
  rw [S_eq_natCast, S_eq_natCast, Snat_add_three]
  push_cast
  ring

/-- Three-step form of the functional equation for `T`. -/
lemma T_add_three (n : ℕ) :
    T n = (((n + 2 : ℕ) : Padic 3) ^ 2) +
      ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * ((n + 3 : ℕ) : Padic 3) *
        T (n + 3) := by
  have h01 := T_succ n
  have h12 := T_succ (n + 1)
  have h23 := T_succ (n + 2)
  calc
    T n = 1 + ((n + 1 : ℕ) : Padic 3) * T (n + 1) := h01
    _ = 1 + ((n + 1 : ℕ) : Padic 3) *
          (1 + ((n + 2 : ℕ) : Padic 3) * T (n + 2)) := by rw [h12]
    _ = 1 + ((n + 1 : ℕ) : Padic 3) +
          ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * T (n + 2) := by ring
    _ = 1 + ((n + 1 : ℕ) : Padic 3) +
          ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) *
            (1 + ((n + 3 : ℕ) : Padic 3) * T (n + 3)) := by rw [h23]
    _ = (1 + ((n + 1 : ℕ) : Padic 3) * (1 + ((n + 2 : ℕ) : Padic 3))) +
          ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * ((n + 3 : ℕ) : Padic 3) *
            T (n + 3) := by ring
    _ = (((n + 2 : ℕ) : Padic 3) ^ 2) +
          ((n + 1 : ℕ) : Padic 3) * ((n + 2 : ℕ) : Padic 3) * ((n + 3 : ℕ) : Padic 3) *
            T (n + 3) := by
        have : (1 : Padic 3) + ((n + 1 : ℕ) : Padic 3) * (1 + ((n + 2 : ℕ) : Padic 3)) =
            (((n + 2 : ℕ) : Padic 3) ^ 2) := by
          push_cast
          ring
        rw [this]

lemma intCast_padic_norm_eq {m : ℤ} (hm : m ≠ 0) :
    ‖(m : Padic 3)‖ = (3 : ℝ) ^ (-(padicValInt 3 m : ℤ)) := by
  have hne : (m : Padic 3) ≠ 0 := by exact_mod_cast hm
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_intCast]
  simp

lemma rat_eq_of_xi (a : ℤ) (b : ℕ) (hb : (b : Padic 3) ≠ 0)
    (heq : xi_3 = (a : Padic 3) / (b : Padic 3)) (n : ℕ) :
    (a : Padic 3) - (b : Padic 3) * S n =
      (b : Padic 3) * (n.factorial : Padic 3) * T n := by
  have h := xi_3_eq_S_add_T n
  rw [heq] at h
  -- a/b = S n + n! * T n  ⇒  a - b * S n = b * n! * T n
  have hsub : (a : Padic 3) / (b : Padic 3) - S n = (n.factorial : Padic 3) * T n := by
    linear_combination h
  have hdiv : (a : Padic 3) / (b : Padic 3) - S n =
      ((a : Padic 3) - (b : Padic 3) * S n) / (b : Padic 3) := by
    field
  rw [hdiv] at hsub
  have hmul := (div_eq_iff hb).mp hsub
  linear_combination hmul

lemma aeval_C_padic (q : ℚ) :
    Polynomial.aeval xi_3 (Polynomial.C q) = algebraMap ℚ (Padic 3) q := by
  simp

/-- A nonzero constant polynomial cannot vanish at `ξ₃`. -/
lemma constant_aeval_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) (hdeg : p.natDegree = 0) :
    Polynomial.aeval xi_3 p ≠ 0 := by
  have hC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have h0 : p.coeff 0 ≠ 0 := by
    intro h
    exact hp (by rw [hC, h, map_zero])
  rw [hC, aeval_C_padic]
  exact (algebraMap ℚ (Padic 3)).injective.ne h0

lemma S_one : S 1 = 1 := by
  simp [S]

lemma T_one : T 1 = xi_3 - 1 := by
  rw [T, S_one, Nat.factorial_one, Nat.cast_one, div_one]

lemma T_one_ne_zero : T 1 ≠ 0 := by
  intro h
  have := xi_3_sub_one_valuation_eq_two
  rw [← T_one, h, _root_.norm_zero] at this
  norm_num at this

/- ### Three-step series for `T` and unique minimal valuation -/

/-- The `m`-th summand in the 3-step expansion of `T n`. -/
noncomputable def Tstep (n m : ℕ) : Padic 3 :=
  (((n + 3 * m + 2 : ℕ) : Padic 3) ^ 2) *
    ∏ i ∈ Finset.range m,
      ((n + 3 * i + 1 : ℕ) : Padic 3) *
        ((n + 3 * i + 2 : ℕ) : Padic 3) *
          ((n + 3 * i + 3 : ℕ) : Padic 3)

lemma Tstep_zero (n : ℕ) :
    Tstep n 0 = (((n + 2 : ℕ) : Padic 3) ^ 2) := by
  simp [Tstep]

lemma prod_three_step (n M : ℕ) :
    ((∏ i ∈ Finset.range M,
        ((n + 3 * i + 1 : ℕ) : Padic 3) *
          ((n + 3 * i + 2 : ℕ) : Padic 3) *
            ((n + 3 * i + 3 : ℕ) : Padic 3))) *
      (((n + 3 * M + 2 : ℕ) : Padic 3) ^ 2) = Tstep n M := by
  simp [Tstep]
  ring

lemma T_eq_partial_Tstep (n M : ℕ) :
    T n = ∑ m ∈ Finset.range M, Tstep n m +
      (∏ i ∈ Finset.range M,
        ((n + 3 * i + 1 : ℕ) : Padic 3) *
          ((n + 3 * i + 2 : ℕ) : Padic 3) *
            ((n + 3 * i + 3 : ℕ) : Padic 3)) * T (n + 3 * M) := by
  induction M with
  | zero =>
    simp [Tstep]
  | succ M ih =>
    have h3 := T_add_three (n + 3 * M)
    rw [ih, Finset.sum_range_succ, add_assoc]
    -- Replace T(n+3M) using the three-step equation, then identify Tstep n M.
    have hmul :=
      congrArg
        (fun t =>
          (∏ i ∈ Finset.range M,
              ((n + 3 * i + 1 : ℕ) : Padic 3) *
                ((n + 3 * i + 2 : ℕ) : Padic 3) *
                  ((n + 3 * i + 3 : ℕ) : Padic 3)) * t)
        h3
    -- The first summand is Tstep n M.
    have hstep : Tstep n M =
        (∏ i ∈ Finset.range M,
            ((n + 3 * i + 1 : ℕ) : Padic 3) *
              ((n + 3 * i + 2 : ℕ) : Padic 3) *
                ((n + 3 * i + 3 : ℕ) : Padic 3)) *
          (((n + 3 * M + 2 : ℕ) : Padic 3) ^ 2) := by
      simp [Tstep]
      ring
    -- The remaining product is the (M+1)-fold product.
    have hprod :
        (∏ i ∈ Finset.range M,
            ((n + 3 * i + 1 : ℕ) : Padic 3) *
              ((n + 3 * i + 2 : ℕ) : Padic 3) *
                ((n + 3 * i + 3 : ℕ) : Padic 3)) *
          (((n + 3 * M + 1 : ℕ) : Padic 3) *
            ((n + 3 * M + 2 : ℕ) : Padic 3) *
              ((n + 3 * M + 3 : ℕ) : Padic 3)) =
          (∏ i ∈ Finset.range (M + 1),
              ((n + 3 * i + 1 : ℕ) : Padic 3) *
                ((n + 3 * i + 2 : ℕ) : Padic 3) *
                  ((n + 3 * i + 3 : ℕ) : Padic 3)) := by
      rw [Finset.prod_range_succ]
    -- Assemble.
    have hnat : n + 3 * M + 3 = n + 3 * (M + 1) := by omega
    calc
      ∑ m ∈ Finset.range M, Tstep n m +
          (∏ i ∈ Finset.range M,
              ((n + 3 * i + 1 : ℕ) : Padic 3) *
                ((n + 3 * i + 2 : ℕ) : Padic 3) *
                  ((n + 3 * i + 3 : ℕ) : Padic 3)) * T (n + 3 * M) =
        ∑ m ∈ Finset.range M, Tstep n m +
          ((∏ i ∈ Finset.range M,
              ((n + 3 * i + 1 : ℕ) : Padic 3) *
                ((n + 3 * i + 2 : ℕ) : Padic 3) *
                  ((n + 3 * i + 3 : ℕ) : Padic 3)) *
            (((n + 3 * M + 2 : ℕ) : Padic 3) ^ 2) +
            (∏ i ∈ Finset.range M,
                ((n + 3 * i + 1 : ℕ) : Padic 3) *
                  ((n + 3 * i + 2 : ℕ) : Padic 3) *
                    ((n + 3 * i + 3 : ℕ) : Padic 3)) *
              (((n + 3 * M + 1 : ℕ) : Padic 3) *
                ((n + 3 * M + 2 : ℕ) : Padic 3) *
                  ((n + 3 * M + 3 : ℕ) : Padic 3)) *
                T (n + 3 * M + 3)) := by
        linear_combination hmul
      _ = ∑ m ∈ Finset.range M, Tstep n m +
            (Tstep n M +
              (∏ i ∈ Finset.range (M + 1),
                  ((n + 3 * i + 1 : ℕ) : Padic 3) *
                    ((n + 3 * i + 2 : ℕ) : Padic 3) *
                      ((n + 3 * i + 3 : ℕ) : Padic 3)) *
                T (n + 3 * (M + 1))) := by
        rw [← hstep, hprod, hnat]

lemma natCast_padic_val_eq {m : ℕ} (hm : m ≠ 0) :
    ‖((m : ℕ) : Padic 3)‖ = (3 : ℝ) ^ (-(padicValNat 3 m : ℤ)) := by
  have hne : ((m : ℕ) : Padic 3) ≠ 0 := by exact_mod_cast hm
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
  simp

lemma padicValNat_of_mod_ne_zero {m : ℕ} (h : ¬ 3 ∣ m) :
    padicValNat 3 m = 0 :=
  (padicValNat.eq_zero_iff).2 (Or.inr (Or.inr h))

/-- If `n ≡ 1 (mod 3)` then only the middle factor in each triple is divisible by 3. -/
lemma val_middle_of_one {n i : ℕ} (hn : n % 3 = 1) :
    padicValNat 3 (n + 3 * i + 1) = 0 ∧
    padicValNat 3 (n + 3 * i + 3) = 0 := by
  constructor
  · apply padicValNat_of_mod_ne_zero
    intro h
    have : (n + 3 * i + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  · apply padicValNat_of_mod_ne_zero
    intro h
    have : (n + 3 * i + 3) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega

lemma n_add_two_not_dvd_nine {n : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    ¬ 9 ∣ n + 2 := by
  intro h9
  have : (n + 2) % 9 = 0 := Nat.dvd_iff_mod_eq_zero.mp h9
  omega

lemma n_add_two_div_three_not_dvd {n : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    ¬ 3 ∣ (n + 2) / 3 := by
  intro hq
  have hdiv : 3 ∣ n + 2 := by
    rcases h with h | h <;> exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have : 9 ∣ n + 2 := by
    have := Nat.mul_dvd_mul_left 3 hq
    rwa [Nat.mul_div_cancel' hdiv] at this
  exact n_add_two_not_dvd_nine h this

lemma n_add_two_div_three_pos {n : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    0 < (n + 2) / 3 := by
  have : 3 ≤ n + 2 := by rcases h with h | h <;> omega
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by omega)

lemma n_add_two_val_one {n : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    padicValNat 3 (n + 2) = 1 := by
  have hdiv : 3 ∣ n + 2 := by
    rcases h with h | h <;> exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hne : (n + 2) / 3 ≠ 0 := (n_add_two_div_three_pos h).ne'
  have hrew : n + 2 = 3 * ((n + 2) / 3) := (Nat.mul_div_cancel' hdiv).symm
  rw [hrew, padicValNat.mul (by norm_num) hne, padicValNat_self,
    padicValNat_of_mod_ne_zero (n_add_two_div_three_not_dvd h)]

lemma val_n_add_three_mul {n i : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    padicValNat 3 (n + 3 * i + 2) = 1 + padicValNat 3 ((n + 2) / 3 + i) := by
  have hdiv : 3 ∣ n + 2 := by
    rcases h with h | h <;> exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hn2 : n + 3 * i + 2 = 3 * ((n + 2) / 3 + i) := by
    have := Nat.mul_div_cancel' hdiv
    omega
  have hne : (n + 2) / 3 + i ≠ 0 := by
    have := n_add_two_div_three_pos h
    omega
  rw [hn2, padicValNat.mul (by norm_num) hne, padicValNat_self]

/-- Integer form of a 3-step summand. -/
def TstepNat (n m : ℕ) : ℕ :=
  (n + 3 * m + 2) ^ 2 *
    ∏ i ∈ Finset.range m, (n + 3 * i + 1) * (n + 3 * i + 2) * (n + 3 * i + 3)

lemma Tstep_eq_natCast (n m : ℕ) :
    Tstep n m = ((TstepNat n m : ℕ) : Padic 3) := by
  simp [Tstep, TstepNat]

lemma TstepNat_pos (n m : ℕ) : 0 < TstepNat n m := by
  unfold TstepNat
  positivity

lemma padicValNat_triple (n i : ℕ) :
    padicValNat 3 ((n + 3 * i + 1) * (n + 3 * i + 2) * (n + 3 * i + 3)) =
      padicValNat 3 (n + 3 * i + 1) +
        padicValNat 3 (n + 3 * i + 2) +
          padicValNat 3 (n + 3 * i + 3) := by
  have h1 : n + 3 * i + 1 ≠ 0 := by omega
  have h2 : n + 3 * i + 2 ≠ 0 := by omega
  have h3 : n + 3 * i + 3 ≠ 0 := by omega
  rw [padicValNat.mul (mul_ne_zero h1 h2) h3, padicValNat.mul h1 h2]

lemma padicValNat_prod_triples (n m : ℕ) :
    padicValNat 3 (∏ i ∈ Finset.range m,
        (n + 3 * i + 1) * (n + 3 * i + 2) * (n + 3 * i + 3)) =
      ∑ i ∈ Finset.range m,
        (padicValNat 3 (n + 3 * i + 1) +
          padicValNat 3 (n + 3 * i + 2) +
            padicValNat 3 (n + 3 * i + 3)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : (∏ i ∈ Finset.range m,
        (n + 3 * i + 1) * (n + 3 * i + 2) * (n + 3 * i + 3)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 ?_
      intro i hi
      positivity
    have hne' : (n + 3 * m + 1) * (n + 3 * m + 2) * (n + 3 * m + 3) ≠ 0 := by
      positivity
    rw [Finset.prod_range_succ, padicValNat.mul hne hne', ih, padicValNat_triple, Finset.sum_range_succ]

lemma padicValNat_Tstep (n m : ℕ) :
    padicValNat 3 (TstepNat n m) =
      2 * padicValNat 3 (n + 3 * m + 2) +
        ∑ i ∈ Finset.range m,
          (padicValNat 3 (n + 3 * i + 1) +
            padicValNat 3 (n + 3 * i + 2) +
              padicValNat 3 (n + 3 * i + 3)) := by
  have hne2 : n + 3 * m + 2 ≠ 0 := by omega
  have hprod : (∏ i ∈ Finset.range m,
      (n + 3 * i + 1) * (n + 3 * i + 2) * (n + 3 * i + 3)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 ?_
    intro i hi
    positivity
  unfold TstepNat
  rw [padicValNat.mul (pow_ne_zero 2 hne2) hprod, padicValNat.pow 2 hne2,
    padicValNat_prod_triples]

lemma padicValNat_Tstep_of_one_four {n m : ℕ}
    (h : n % 9 = 1 ∨ n % 9 = 4) :
    padicValNat 3 (TstepNat n m) =
      m + 2 + 2 * padicValNat 3 ((n + 2) / 3 + m) +
        ∑ i ∈ Finset.range m, padicValNat 3 ((n + 2) / 3 + i) := by
  have hn : n % 3 = 1 := by rcases h with h | h <;> omega
  rw [padicValNat_Tstep]
  have hmid : ∀ i, padicValNat 3 (n + 3 * i + 2) =
      1 + padicValNat 3 ((n + 2) / 3 + i) :=
    fun i => val_n_add_three_mul (i := i) h
  have hsides : ∀ i,
      padicValNat 3 (n + 3 * i + 1) = 0 ∧
        padicValNat 3 (n + 3 * i + 3) = 0 :=
    fun i => val_middle_of_one (n := n) (i := i) hn
  simp only [hmid, (hsides _).1, (hsides _).2, zero_add, add_zero]
  have hsum : ∑ i ∈ Finset.range m, (1 + padicValNat 3 ((n + 2) / 3 + i)) =
      m + ∑ i ∈ Finset.range m, padicValNat 3 ((n + 2) / 3 + i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    simp
  rw [hsum]
  omega

lemma padicValNat_Tstep_zero_of_one_four {n : ℕ}
    (h : n % 9 = 1 ∨ n % 9 = 4) :
    padicValNat 3 (TstepNat n 0) = 2 := by
  rw [padicValNat_Tstep_of_one_four h]
  simp [padicValNat_of_mod_ne_zero (n_add_two_div_three_not_dvd h)]

lemma padicValNat_Tstep_ge {n m : ℕ}
    (h : n % 9 = 1 ∨ n % 9 = 4) :
    m + 2 ≤ padicValNat 3 (TstepNat n m) := by
  rw [padicValNat_Tstep_of_one_four h]
  omega

lemma norm_Tstep_zero_of_one_four {n : ℕ}
    (h : n % 9 = 1 ∨ n % 9 = 4) :
    ‖Tstep n 0‖ = (3 : ℝ) ^ (-(2 : ℤ)) := by
  rw [Tstep_eq_natCast, natCast_padic_val_eq (TstepNat_pos n 0).ne',
    padicValNat_Tstep_zero_of_one_four h]
  norm_cast

lemma norm_Tstep_le_of_one_four {n m : ℕ}
    (h : n % 9 = 1 ∨ n % 9 = 4) :
    ‖Tstep n m‖ ≤ (3 : ℝ) ^ (-((m + 2 : ℕ) : ℤ)) := by
  rw [Tstep_eq_natCast, natCast_padic_val_eq (TstepNat_pos n m).ne']
  have hge := padicValNat_Tstep_ge (n := n) (m := m) h
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
  exact Int.neg_le_neg (by exact_mod_cast hge)

lemma rem_prod_norm_le {n M : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    ‖(∏ i ∈ Finset.range M,
        ((n + 3 * i + 1 : ℕ) : Padic 3) *
          ((n + 3 * i + 2 : ℕ) : Padic 3) *
            ((n + 3 * i + 3 : ℕ) : Padic 3))‖ ≤
      (3 : ℝ)⁻¹ ^ M := by
  have hn : n % 3 = 1 := by rcases h with h | h <;> omega
  have hnorm : ∀ i : ℕ,
      ‖((n + 3 * i + 1 : ℕ) : Padic 3) *
          ((n + 3 * i + 2 : ℕ) : Padic 3) *
            ((n + 3 * i + 3 : ℕ) : Padic 3)‖ ≤ (3 : ℝ)⁻¹ := by
    intro i
    have h1 : ‖((n + 3 * i + 1 : ℕ) : Padic 3)‖ = 1 := by
      have hne : ((n + 3 * i + 1 : ℕ) : Padic 3) ≠ 0 := by
        exact_mod_cast (by omega : n + 3 * i + 1 ≠ 0)
      rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
      have : padicValNat 3 (n + 3 * i + 1) = 0 := (val_middle_of_one hn).1
      simp [this]
    have h3 : ‖((n + 3 * i + 3 : ℕ) : Padic 3)‖ = 1 := by
      have hne : ((n + 3 * i + 3 : ℕ) : Padic 3) ≠ 0 := by
        exact_mod_cast (by omega : n + 3 * i + 3 ≠ 0)
      rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
      have : padicValNat 3 (n + 3 * i + 3) = 0 := (val_middle_of_one hn).2
      simp [this]
    have h2 : ‖((n + 3 * i + 2 : ℕ) : Padic 3)‖ ≤ (3 : ℝ)⁻¹ := by
      have : n + 3 * i + 2 = (n + 2) + 3 * i := by omega
      rw [this]
      exact natCast_padic_norm_le_inv_three (by
        have hdiv' : 3 ∣ n + 2 := by
          rcases h with h | h <;> exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
        exact dvd_add hdiv' (dvd_mul_right _ _))
    rw [norm_mul, norm_mul, h1, h3, one_mul, mul_one]
    exact h2
  rw [norm_prod]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.prod_range_succ]
    exact mul_le_mul ih (hnorm M) (norm_nonneg _) (pow_nonneg (by norm_num) _)

lemma rem_prod_val_ge {n M : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    ‖(∏ i ∈ Finset.range M,
        ((n + 3 * i + 1 : ℕ) : Padic 3) *
          ((n + 3 * i + 2 : ℕ) : Padic 3) *
            ((n + 3 * i + 3 : ℕ) : Padic 3))‖ ≤
      (3 : ℝ) ^ (-(M : ℤ)) := by
  have hle := rem_prod_norm_le (n := n) (M := M) h
  have heq : (3 : ℝ)⁻¹ ^ M = (3 : ℝ) ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rwa [heq] at hle

/-- For `n ≡ 1,4 (mod 9)`, `‖T n‖ = 3⁻²`. -/
lemma T_norm_eq_nine_inv {n : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    ‖T n‖ = (3 : ℝ) ^ (-(2 : ℤ)) := by
  -- Expand far enough that the remainder is smaller than the unique minimal term.
  have hexp := T_eq_partial_Tstep n 4
  have hlead : ‖Tstep n 0‖ = (3 : ℝ) ^ (-(2 : ℤ)) :=
    norm_Tstep_zero_of_one_four h
  have hterms : ∀ m ∈ Finset.Ico 1 4,
      ‖Tstep n m‖ ≤ (3 : ℝ) ^ (-(3 : ℤ)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have := norm_Tstep_le_of_one_four (n := n) (m := m) h
    refine le_trans this ?_
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    apply Int.neg_le_neg
    exact_mod_cast (by omega : 3 ≤ m + 2)
  have hsum0 :
      ∑ m ∈ Finset.range 4, Tstep n m - Tstep n 0 =
        ∑ m ∈ Finset.Ico 1 4, Tstep n m := by
    have hset : Finset.range 4 = insert 0 (Finset.Ico 1 4) := by
      ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  have hsum :
      ‖∑ m ∈ Finset.range 4, Tstep n m - Tstep n 0‖ ≤
        (3 : ℝ) ^ (-(3 : ℤ)) := by
    rw [hsum0]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro m hm
    exact hterms m hm
  have hrem :
      ‖(∏ i ∈ Finset.range 4,
          ((n + 3 * i + 1 : ℕ) : Padic 3) *
            ((n + 3 * i + 2 : ℕ) : Padic 3) *
              ((n + 3 * i + 3 : ℕ) : Padic 3)) * T (n + 12)‖ ≤
        (3 : ℝ) ^ (-(3 : ℤ)) := by
    rw [norm_mul]
    have hp := rem_prod_val_ge (n := n) (M := 4) h
    have hT : ‖T (n + 12)‖ ≤ 1 := T_norm_le_one _
    have hle4 : (3 : ℝ) ^ (-(4 : ℤ)) * ‖T (n + 12)‖ ≤ (3 : ℝ) ^ (-(4 : ℤ)) :=
      mul_le_of_le_one_right (zpow_nonneg (by norm_num) _) hT
    have h34 : (3 : ℝ) ^ (-(4 : ℤ)) ≤ (3 : ℝ) ^ (-(3 : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      norm_num
    exact ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hle4).trans h34
  have hrest : ‖T n - Tstep n 0‖ < ‖Tstep n 0‖ := by
    have : T n - Tstep n 0 =
        (∑ m ∈ Finset.range 4, Tstep n m - Tstep n 0) +
          (∏ i ∈ Finset.range 4,
              ((n + 3 * i + 1 : ℕ) : Padic 3) *
                ((n + 3 * i + 2 : ℕ) : Padic 3) *
                  ((n + 3 * i + 3 : ℕ) : Padic 3)) * T (n + 12) := by
      linear_combination hexp
    rw [this, hlead]
    have hbound :=
      (IsUltrametricDist.norm_add_le_max
        (∑ m ∈ Finset.range 4, Tstep n m - Tstep n 0)
        ((∏ i ∈ Finset.range 4,
            ((n + 3 * i + 1 : ℕ) : Padic 3) *
              ((n + 3 * i + 2 : ℕ) : Padic 3) *
                ((n + 3 * i + 3 : ℕ) : Padic 3)) * T (n + 12))).trans
        (max_le hsum hrem)
    refine lt_of_le_of_lt hbound ?_
    apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 3)
    norm_num
  have : ‖T n‖ = ‖Tstep n 0‖ :=
    padic_norm_eq_of_norm_sub_lt (x := T n) (y := Tstep n 0) hrest
  rw [this, hlead]

lemma T_ne_zero_of_one_four {n : ℕ} (h : n % 9 = 1 ∨ n % 9 = 4) :
    T n ≠ 0 := by
  intro ht
  have := T_norm_eq_nine_inv h
  rw [ht, _root_.norm_zero] at this
  norm_num at this

lemma T_ne_zero_of_mod_ne_seven {n : ℕ} (h : n % 9 ≠ 7) : T n ≠ 0 := by
  have : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨
      n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 8 := by omega
  rcases this with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h8
  · exact T_ne_zero_of_zero (by omega)
  · exact T_ne_zero_of_one_four (Or.inl h1)
  · exact T_ne_zero_of_two (by omega)
  · exact T_ne_zero_of_zero (by omega)
  · exact T_ne_zero_of_one_four (Or.inr h4)
  · exact T_ne_zero_of_two (by omega)
  · exact T_ne_zero_of_zero (by omega)
  · exact T_ne_zero_of_two (by omega)

lemma xi_3_ne_S_of_mod_ne_seven {n : ℕ} (h : n % 9 ≠ 7) : xi_3 ≠ S n := by
  intro heq
  have hT : T n = 0 := by
    have hmul := T_mul_factorial n
    rw [heq, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (factorial_ne_zero_padic n)
  exact T_ne_zero_of_mod_ne_seven h hT

/--
Conjecture: this constant is transcendental, which means that it is not the root of any polynomial with integer coefficients.

Formally, $\xi_3$ is not algebraic over $\mathbb{Q}$.
-/
theorem oeis_341685_conjecture_0 : ¬ IsAlgebraic ℚ (xi_3) := by
  intro h
  obtain ⟨P, hP0, hProot⟩ := h
  have hdeg_pos : 0 < P.natDegree := by
    by_contra hdeg
    have : P.natDegree = 0 := by omega
    exact constant_aeval_ne_zero hP0 this hProot
  -- Positive degree: ξ₃ is transcendental.
  sorry



