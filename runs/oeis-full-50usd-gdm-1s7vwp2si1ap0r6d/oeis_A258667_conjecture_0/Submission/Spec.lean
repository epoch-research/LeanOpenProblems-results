import FormalConjectures.Util.ProblemImports

open BigOperators Nat Int Real Asymptotics Filter

/--
The inner sum of the formula used in A258667:
$$\sum_{\max(k-n+5, 0) \le j \le \min(k,4)} \binom{8-j}{j}\binom{2n-k+j-10}{k-j}$$
-/
private def A258667_inner_sum (n k : ℕ) : ℤ :=
  let L : ℕ := max 0 (k + 5 - n)
  let U : ℕ := min k 4
  Finset.sum (Finset.Icc L U) fun j =>
    let term1 := Nat.choose (8 - j) j
    -- The top argument of the second binomial coefficient is written in Nat subtraction form.
    let term2 := Nat.choose (2 * n + j - (k + 10)) (k - j)
    ofNat term1 * ofNat term2

/--
A258667: A total of $n$ married couples, including a mathematician M and his wife, are to be seated at the $2n$ chairs around a circular table, with no man seated next to his wife. After the ladies are seated at every other chair, M is the first man allowed to choose one of the remaining chairs. The sequence gives the number of ways of seating the other men, with no man seated next to his wife, if M chooses the chair that is 9 seats clockwise from his wife's chair.

$$a(n) = \begin{cases} 0 & \text{if } n \le 5 \\ \sum_{k=0}^{n-1}(-1)^k(n-k-1)! \sum_{\max(k-n+5, 0) \le j \le \min(k,4)} \binom{8-j}{j}\binom{2n-k+j-10}{k-j} & \text{if } n > 5 \end{cases}$$
-/
def A258667 (n : ℕ) : ℕ :=
  if h : n ≤ 5 then 0 else
  (Finset.sum (Finset.range n) fun k =>
    let sign : ℤ := if k % 2 = 0 then 1 else -1
    -- Nat.factorial (n - 1 - k) is safe since h implies n > 5 and k < n.
    let fac_term : ℤ := ofNat (Nat.factorial (n - 1 - k))

    sign * fac_term * A258667_inner_sum n k
  ).natAbs

-- Start of formalization of the conjecture

noncomputable def nat_fac_to_real (n : ℕ) : ℝ := (Nat.factorial n : ℝ)

/-- The denominator term $k! (n-1)_k$ represented as a Real number. -/
noncomputable def menage_denom_term (n k : ℕ) : ℝ :=
  let k_fac_R := nat_fac_to_real k
  -- (n-1)_k is the falling factorial. Nat.descFactorial (n-1) k is (n-1)!/(n-1-k)!
  let falling_fac := (Nat.descFactorial (n - 1) k : ℝ)
  k_fac_R * falling_fac

/-- The infinite series part of the asymptotic expansion: $\sum_{k \ge 1} \frac{(-1)^k}{k!(n-1)_k}$. -/
noncomputable def A258667_asymptotic_sum_part (n : ℕ) : ℝ :=
  -- The sum is effectively finite since (n-1)_k is 0 for k >= n.
  Finset.sum (Finset.range n) fun k =>
    if k = 0 then 0
    else
      let denom := menage_denom_term n k
      -- Denominator is non-zero if n >= 1 and 1 <= k < n.
      if denom = 0 then 0
      else ((-1 : ℝ) ^ k) / denom

/-- The proposed asymptotic expression for A258667(n). -/
noncomputable def A258667_asymptotic_term (n : ℕ) : ℝ :=
  if n ≤ 2 then 0 -- Avoid division by zero, irrelevant for n -> infinity
  else
    let n_R : ℝ := n
    let n_fac_R := nat_fac_to_real n
    let prefactor : ℝ := exp (-2) * (n_fac_R / (n_R - 2))
    prefactor * (1 + A258667_asymptotic_sum_part n)

/--
A258667 Conjecture:
Therefore, it is natural to conjecture that a(n) ~ e^(-2)*n!/(n-2)*(1 + Sum_{k>=1} (-1)^k/(k!(n-1)_k)).
-/




lemma descFactorial_ge_two (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) :
    (n - 1) * (n - 2) ≤ Nat.descFactorial (n - 1) k := by
  have hn2 : 2 ≤ n - 1 := by omega
  have h_mul := Nat.descFactorial_mul_descFactorial (n := n - 1) (k := 2) (m := k) hk
  have h_two : Nat.descFactorial (n - 1) 2 = (n - 1) * (n - 2) := by
    have : n - 1 - 1 = n - 2 := by omega
    simp [Nat.descFactorial_succ, this]
    ring
  rw [← h_mul, h_two]
  have h_pos : 0 < Nat.descFactorial (n - 1 - 2) (k - 2) := by
    rw [Nat.descFactorial_pos]
    omega
  have h_ge_one : 1 ≤ Nat.descFactorial (n - 1 - 2) (k - 2) := h_pos
  have h_le := Nat.mul_le_mul_right ((n - 1) * (n - 2)) h_ge_one
  rw [Nat.one_mul] at h_le
  exact h_le

lemma menage_denom_term_ge (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) :
    2 * (((n - 1) * (n - 2) : ℕ) : ℝ) ≤ menage_denom_term n k := by
  have h1 : (2 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    have : 2 ≤ Nat.factorial k := by
      have h_fac := Nat.factorial_le hk
      exact h_fac
    exact_mod_cast this
  have h2 : (((n - 1) * (n - 2) : ℕ) : ℝ) ≤ (Nat.descFactorial (n - 1) k : ℝ) := by
    have h_desc := descFactorial_ge_two n k hk hn
    exact_mod_cast h_desc
  unfold menage_denom_term nat_fac_to_real
  have h3 : (0 : ℝ) ≤ (((n - 1) * (n - 2) : ℕ) : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ (Nat.descFactorial (n - 1) k : ℝ) := by positivity
  nlinarith

lemma term_bound (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) (hn3 : 3 ≤ n) :
    |((-1 : ℝ)^k) / menage_denom_term n k| ≤ 1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
  have h_denom : 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) ≤ menage_denom_term n k := menage_denom_term_ge n k hk hn
  have h_pos_denom : 0 < 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) := by
    have : 0 < (n - 1) * (n - 2) := by
      have : n - 1 ≥ 2 := by omega
      have : n - 2 ≥ 1 := by omega
      positivity
    positivity
  have h_abs_num : |(-1 : ℝ)^k| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have h_abs_denom : |menage_denom_term n k| = menage_denom_term n k := by
    have : 0 < menage_denom_term n k := by linarith
    exact abs_of_pos this
  rw [abs_div, h_abs_num, h_abs_denom]
  have h_le : 1 / menage_denom_term n k ≤ 1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
    rw [_root_.one_div_le_one_div] <;> linarith
  exact h_le

lemma sum_range_split (m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 2), f i = f 0 + f 1 + ∑ i ∈ Finset.range m, f (i + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  ring

lemma sum_part_eq (n : ℕ) (hn3 : 3 ≤ n) :
    A258667_asymptotic_sum_part n = -1 / (n - 1 : ℝ) + ∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2) := by
  unfold A258667_asymptotic_sum_part
  have h_eq : n = (n - 2) + 2 := by omega
  have h_add : n - 2 + 2 = n := by omega
  conv_lhs => rw [h_eq]
  rw [sum_range_split (n - 2)]
  simp_rw [h_add]
  have h1 : (if 1 = 0 then (0 : ℝ) else if menage_denom_term n 1 = 0 then 0 else (-1) ^ 1 / menage_denom_term n 1) = -1 / (n - 1 : ℝ) := by
    have h1_ne : 1 ≠ 0 := by decide
    rw [if_neg h1_ne]
    have h_denom : menage_denom_term n 1 = (((n - 1 : ℕ) : ℝ)) := by
      unfold menage_denom_term nat_fac_to_real
      have h_desc : Nat.descFactorial (n - 1) 1 = n - 1 := Nat.descFactorial_one (n - 1)
      have h_fac : Nat.factorial 1 = 1 := rfl
      rw [h_desc, h_fac]
      simp
    have h_denom_ne : (menage_denom_term n 1 : ℝ) ≠ 0 := by
      rw [h_denom]
      have : n - 1 ≠ 0 := by omega
      exact_mod_cast this
    rw [if_neg h_denom_ne, h_denom]
    have h_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h_sub_raw : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ) := Nat.cast_sub (show 1 ≤ n by omega)
      rw [h_sub_raw]
      simp
    rw [h_sub]
    ring
  have h2 (k : ℕ) (hk : k < n - 2) :
      (if k + 2 = 0 then (0 : ℝ) else if menage_denom_term n (k + 2) = 0 then 0 else (-1) ^ (k + 2) / menage_denom_term n (k + 2)) =
      (-1) ^ (k + 2) / menage_denom_term n (k + 2) := by
    have h_ne : k + 2 ≠ 0 := by omega
    rw [if_neg h_ne]
    have h_denom_ne : menage_denom_term n (k + 2) ≠ 0 := by
      have hk2 : 2 ≤ k + 2 := by omega
      have hkn : k + 2 < n := by omega
      have h_ge := menage_denom_term_ge n (k + 2) hk2 hkn
      have h_pos : 0 < 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) := by
        have : 0 < (n - 1) * (n - 2) := by
          have : n - 1 ≥ 2 := by omega
          have : n - 2 ≥ 1 := by omega
          positivity
        positivity
      linarith
    rw [if_neg h_denom_ne]
  rw [if_pos True.intro, h1, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact h2 k hk

lemma asymptotic_sum_part_bound (n : ℕ) (hn3 : 3 ≤ n) :
    |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
  rw [sum_part_eq n hn3]
  have h_tri : |-1 / (n - 1 : ℝ) + ∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| ≤
               |-1 / (n - 1 : ℝ)| + |∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| := abs_add_le _ _
  have h_term1 : |-1 / (n - 1 : ℝ)| = 1 / (n - 1 : ℝ) := by
    have : (n : ℝ) - 1 > 0 := by
      have : (n : ℝ) ≥ 3 := by exact_mod_cast hn3
      linarith
    rw [abs_div, abs_neg, abs_one]
    rw [abs_of_pos this]
  have h_term2 : |∑ k ∈ Finset.range (n - 2), ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| ≤
                 (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
    have h_abs_sum := Finset.abs_sum_le_sum_abs (s := Finset.range (n - 2)) (f := fun k => ((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2))
    have h_sum_le : ∑ k ∈ Finset.range (n - 2), |((-1 : ℝ)^(k + 2)) / menage_denom_term n (k + 2)| ≤
                    ∑ k ∈ Finset.range (n - 2), 1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      have hk2 : 2 ≤ k + 2 := by omega
      have hkn : k + 2 < n := by omega
      exact term_bound n (k + 2) hk2 hkn hn3
    have h_sum_const : ∑ k ∈ Finset.range (n - 2), (1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ))) =
                      ((n - 2 : ℕ) : ℝ) * (1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ))) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    have h_le : ((n - 2 : ℕ) : ℝ) * (1 / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ))) ≤
                (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) := by
      have : ((n - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : n - 2 ≤ n := by omega
        exact_mod_cast this
      have h_pos : 0 < 2 * (((n - 1) * (n - 2) : ℕ) : ℝ) := by
        have : 0 < (n - 1) * (n - 2) := by
          have : n - 1 ≥ 2 := by omega
          have : n - 2 ≥ 1 := by omega
          positivity
        positivity
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right this h_pos.le
    linarith [h_abs_sum, h_sum_le, h_sum_const, h_le]
  linarith

lemma second_term_bound (n : ℕ) (hn4 : 4 ≤ n) :
    (n : ℝ) / (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) ≤ 1 / (n - 3 : ℝ) := by
  have h_sub1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h_sub_raw : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ) := Nat.cast_sub (show 1 ≤ n by omega)
    rw [h_sub_raw]; simp
  have h_sub2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    have h_sub_raw : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - ((2 : ℕ) : ℝ) := Nat.cast_sub (show 2 ≤ n by omega)
    rw [h_sub_raw]; simp
  have h_denom : (2 * (((n - 1) * (n - 2) : ℕ) : ℝ)) = 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    push_cast
    rw [h_sub1, h_sub2]
    ring
  rw [h_denom]
  have h_pos1 : (n : ℝ) - 3 > 0 := by
    have : (n : ℝ) ≥ 4 := by exact_mod_cast hn4
    linarith
  have h_pos2 : 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) > 0 := by
    have : (n : ℝ) ≥ 4 := by exact_mod_cast hn4
    nlinarith
  have h_le : (n : ℝ) * ((n : ℝ) - 3) ≤ 2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have : (n : ℝ) ≥ 4 := by exact_mod_cast hn4
    nlinarith
  rw [div_le_iff₀ h_pos2, one_div_mul_eq_div, le_div_iff₀ h_pos1]
  exact h_le

lemma tendsto_two_div_n : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (nhds 0) := by
  have h_eq : (0 : ℝ) = 2 * 0 := by ring
  conv_rhs => rw [h_eq]
  have h_mul : Tendsto (fun n : ℕ => 2 * (1 / (n : ℝ))) atTop (nhds (2 * 0)) := by
    exact Tendsto.mul tendsto_const_nhds tendsto_one_div_atTop_nhds_zero_nat
  simp_rw [mul_one_div] at h_mul
  exact h_mul

lemma tendsto_one_div_sub_one : Tendsto (fun n : ℕ => 1 / (n - 1 : ℝ)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 2 / (n : ℝ)) ?_ tendsto_two_div_n ?_ ?_
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h_n : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 1 > 0 := by linarith
    exact div_nonneg (by linarith) h_pos.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h_n : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 1 > 0 := by linarith
    have h_pos_n : (n : ℝ) > 0 := by linarith
    rw [div_le_div_iff₀ h_pos h_pos_n]
    linarith

lemma tendsto_one_div_sub_three : Tendsto (fun n : ℕ => 1 / (n - 3 : ℝ)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 2 / (n : ℝ)) ?_ tendsto_two_div_n ?_ ?_
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have h_n : (n : ℝ) ≥ 4 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 3 > 0 := by linarith
    exact div_nonneg (by linarith) h_pos.le
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have h_n : (n : ℝ) ≥ 6 := by exact_mod_cast hn
    have h_pos : (n : ℝ) - 3 > 0 := by linarith
    have h_pos_n : (n : ℝ) > 0 := by linarith
    rw [div_le_div_iff₀ h_pos h_pos_n]
    linarith


lemma asymptotic_sum_part_bound_four (n : ℕ) (hn4 : 4 ≤ n) :
    |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := by
  have h1 := asymptotic_sum_part_bound n (by omega)
  have h2 := second_term_bound n hn4
  linarith

lemma tendsto_asymptotic_sum_part : Tendsto A258667_asymptotic_sum_part atTop (nhds 0) := by
  have h_bound : ∀ᶠ (n : ℕ) in atTop, |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    exact asymptotic_sum_part_bound_four n hn
  have h_limit : Tendsto (fun n : ℕ => 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ)) atTop (nhds 0) := by
    have : (0 : ℝ) = 0 + 0 := by ring
    conv_rhs => rw [this]
    exact Tendsto.add tendsto_one_div_sub_one tendsto_one_div_sub_three
  have h_limit_neg : Tendsto (fun n : ℕ => - (1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ))) atTop (nhds 0) := by
    have : (0 : ℝ) = -0 := by ring
    conv_rhs => rw [this]
    exact Tendsto.neg h_limit
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (n : ℕ) => - (1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ))) (h := fun (n : ℕ) => 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ)) h_limit_neg h_limit ?_ ?_
  · filter_upwards [h_bound] with n hn
    have : |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := hn
    rw [abs_le] at this
    exact this.1
  · filter_upwards [h_bound] with n hn
    have : |A258667_asymptotic_sum_part n| ≤ 1 / (n - 1 : ℝ) + 1 / (n - 3 : ℝ) := hn
    rw [abs_le] at this
    exact this.2


lemma eventually_one_add_sum_part_ne_zero : ∀ᶠ (n : ℕ) in atTop, 1 + A258667_asymptotic_sum_part n ≠ 0 := by
  have h_limit : Tendsto (fun n => 1 + A258667_asymptotic_sum_part n) atTop (nhds (1 + 0)) := by
    exact Tendsto.const_add 1 tendsto_asymptotic_sum_part
  have h_ne : (1 : ℝ) + 0 ≠ 0 := by linarith
  exact Tendsto.eventually_ne h_limit h_ne


lemma eventually_asymptotic_term_ne_zero : ∀ᶠ (x : ℕ) in atTop, A258667_asymptotic_term x ≠ 0 := by
  filter_upwards [eventually_ge_atTop 3, eventually_one_add_sum_part_ne_zero] with x hx1 hx2
  unfold A258667_asymptotic_term
  have : ¬ x ≤ 2 := by omega
  simp [this]
  have h_exp : exp (-2) ≠ 0 := by
    have : exp (-2) > 0 := exp_pos (-2)
    linarith
  have h_fac : nat_fac_to_real x ≠ 0 := by
    unfold nat_fac_to_real
    have : (x.factorial : ℝ) > 0 := by positivity
    linarith
  have h_div : (x : ℝ) - 2 ≠ 0 := by
    have : (x : ℝ) ≥ 3 := by exact_mod_cast hx1
    linarith
  exact ⟨⟨h_fac, h_div⟩, hx2⟩

theorem first_goal_proof : ∀ᶠ (x : ℕ) in atTop, A258667_asymptotic_term x = 0 → (A258667 x : ℝ) = 0 := by
  filter_upwards [eventually_asymptotic_term_ne_zero] with x hx
  intro h
  exact (hx h).elim





lemma sign_eq_pow_neg_one (k : ℕ) : (if k % 2 = 0 then (1 : ℝ) else -1) = (-1 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rw [← ih]
    have h_mod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h_mod with h | h
    · have h_succ : (k + 1) % 2 = 1 := by omega
      have h_succ_ne : (k + 1) % 2 ≠ 0 := by omega
      simp [h, h_succ_ne]
    · have h_succ : (k + 1) % 2 = 0 := by omega
      simp [h, h_succ]

lemma A258667_formula (n : ℕ) (hn : 5 < n) :
    (A258667 n : ℝ) = |∑ k ∈ Finset.range n, (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)| * nat_fac_to_real (n - 1) := by
  unfold A258667
  have h_not : ¬ n ≤ 5 := by omega
  simp [h_not]
  have h_pos_fac : 0 < nat_fac_to_real (n - 1) := by
    unfold nat_fac_to_real
    positivity
  rw [← abs_of_pos h_pos_fac]
  rw [← abs_mul]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have h_split : (if k % 2 = 0 then (Nat.factorial (n - 1 - k) : ℝ) * (A258667_inner_sum n k : ℝ) else -((Nat.factorial (n - 1 - k) : ℝ) * (A258667_inner_sum n k : ℝ))) = (if k % 2 = 0 then (1 : ℝ) else -1) * (Nat.factorial (n - 1 - k) : ℝ) * (A258667_inner_sum n k : ℝ) := by
    split_ifs with h_cond
    · ring
    · ring
  rw [h_split]
  have h_sign : (if k % 2 = 0 then (1 : ℝ) else -1) = (-1 : ℝ)^k := sign_eq_pow_neg_one k
  have h_desc : (Nat.descFactorial (n - 1) k : ℝ) * (Nat.factorial (n - 1 - k) : ℝ) = nat_fac_to_real (n - 1) := by
    unfold nat_fac_to_real
    have h_eq : (n - 1 - k).factorial * (n - 1).descFactorial k = (n - 1).factorial := by
      exact Nat.factorial_mul_descFactorial (by omega)
    rw [mul_comm]
    exact_mod_cast h_eq
  have h_desc_ne : (Nat.descFactorial (n - 1) k : ℝ) ≠ 0 := by
    have h_pos : 0 < Nat.descFactorial (n - 1) k := by
      rw [Nat.descFactorial_pos]
      omega
    positivity
  have h_div : (Nat.factorial (n - 1 - k) : ℝ) = nat_fac_to_real (n - 1) / (Nat.descFactorial (n - 1) k : ℝ) := by
    rw [← h_desc]
    rw [mul_comm, mul_div_cancel_right₀ _ h_desc_ne]
  rw [h_sign, h_div]
  unfold nat_fac_to_real
  ring

lemma tendsto_n_div_n_sub_two : Tendsto (fun n : ℕ => (n : ℝ) / (n - 2 : ℝ)) atTop (nhds 1) := by
  have h_eq : (fun n : ℕ => (n : ℝ) / (n - 2 : ℝ)) =ᶠ[atTop] (fun n : ℕ => 1 + 2 / (n - 2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have h_pos : (n : ℝ) - 2 ≠ 0 := by
      have : (n : ℝ) ≥ 3 := by exact_mod_cast hn
      linarith
    field_simp
    ring
  rw [tendsto_congr' h_eq]
  have h_lim : Tendsto (fun n : ℕ => 2 / (n - 2 : ℝ)) atTop (nhds 0) := by
    have h_bound : ∀ x ≥ 4, 0 ≤ 2 / ((x : ℝ) - 2) ∧ 2 / ((x : ℝ) - 2) ≤ 4 / (x : ℝ) := by
      intro x hx
      have h1 : (x : ℝ) - 2 > 0 := by linarith
      have h2 : (x : ℝ) > 0 := by linarith
      constructor
      · positivity
      · rw [div_le_div_iff₀ h1 h2]
        linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := fun (n : ℕ) => 2 / ((n : ℝ) - 2)) (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 4 / (n : ℝ)) ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · have h_eq : (fun n : ℕ => 4 / (n : ℝ)) = (fun n : ℕ => (1 / (n : ℝ)) * 4) := by
        ext n
        ring
      rw [h_eq]
      have h_zero : (0 : ℝ) = 0 * 4 := by ring
      rw [h_zero]
      exact Tendsto.mul_const 4 tendsto_one_div_atTop_nhds_zero_nat
    · filter_upwards [eventually_ge_atTop 4] with n hn
      have h_cast : (n : ℝ) ≥ 4 := by exact_mod_cast hn
      exact (h_bound (n : ℝ) h_cast).1
    · filter_upwards [eventually_ge_atTop 4] with n hn
      have h_cast : (n : ℝ) ≥ 4 := by exact_mod_cast hn
      exact (h_bound (n : ℝ) h_cast).2
  have h_one : (1 : ℝ) = 1 + 0 := by ring
  conv_rhs => rw [h_one]
  exact Tendsto.const_add 1 h_lim

lemma tendsto_denom (h_sum : Tendsto A258667_asymptotic_sum_part atTop (nhds 0)) :
    Tendsto (fun n : ℕ => exp (-2) * (((n : ℝ) / (n - 2 : ℝ)) * (1 + A258667_asymptotic_sum_part n))) atTop (nhds (exp (-2))) := by
  have h_one : (exp (-2) : ℝ) = exp (-2) * (1 * (1 + 0)) := by ring
  conv_rhs => rw [h_one]
  apply Tendsto.const_mul
  apply Tendsto.mul
  · exact tendsto_n_div_n_sub_two
  · exact Tendsto.const_add 1 h_sum
















lemma factorial_step (n : ℕ) (hn : 1 ≤ n) :
    nat_fac_to_real n = (n : ℝ) * nat_fac_to_real (n - 1) := by
  unfold nat_fac_to_real
  have : n = (n - 1) + 1 := by omega
  nth_rw 1 [this]
  rw [Nat.factorial_succ]
  push_cast
  have h_add : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  rw [h_add]

lemma asymp_term_ratio_eq (n : ℕ) (hn : 3 ≤ n) :
    A258667_asymptotic_term n / (exp (-2) * nat_fac_to_real (n - 1)) = (n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n) := by
  unfold A258667_asymptotic_term
  have h_not_le : ¬ n ≤ 2 := by omega
  simp [h_not_le]
  rw [factorial_step n (by omega)]
  have h_exp : exp (-2) ≠ 0 := by
    have : exp (-2) > 0 := exp_pos (-2)
    linarith
  have h_fac : nat_fac_to_real (n - 1) ≠ 0 := by
    unfold nat_fac_to_real
    have : ((n - 1).factorial : ℝ) > 0 := by positivity
    linarith
  have h_sub : (n : ℝ) - 2 ≠ 0 := by
    have : (n : ℝ) ≥ 3 := by exact_mod_cast hn
    linarith
  field_simp

lemma ratio_eq (n : ℕ) (hn : 5 < n) :
    (A258667 n : ℝ) / A258667_asymptotic_term n =
    |∑ k ∈ Finset.range n, (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)| / (exp (-2) * ((n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n))) := by
  have h_asymp : A258667_asymptotic_term n = (n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n) * (exp (-2) * nat_fac_to_real (n - 1)) := by
    have h_div := asymp_term_ratio_eq n (by omega)
    have h_ne : exp (-2) * nat_fac_to_real (n - 1) ≠ 0 := by
      have h_exp : exp (-2) > 0 := exp_pos (-2)
      have h_fac : nat_fac_to_real (n - 1) > 0 := by
        unfold nat_fac_to_real
        positivity
      positivity
    rw [div_eq_iff h_ne] at h_div
    rw [h_div]
  rw [A258667_formula n hn, h_asymp]
  have h_fac_ne : nat_fac_to_real (n - 1) ≠ 0 := by
    unfold nat_fac_to_real
    positivity
  field_simp

lemma h1_proof : IsEquivalent atTop A258667_asymptotic_term (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
  refine isEquivalent_of_tendsto_one' ?_ ?_
  · intro n hn
    have h_exp : exp (-2) > 0 := exp_pos (-2)
    have h_fac : nat_fac_to_real (n - 1) > 0 := by
      unfold nat_fac_to_real
      positivity
    have : exp (-2) * nat_fac_to_real (n - 1) > 0 := mul_pos h_exp h_fac
    linarith
  · change Tendsto (fun n => A258667_asymptotic_term n / (exp (-2) * nat_fac_to_real (n - 1))) atTop (nhds 1)
    have h_eq : (fun n => A258667_asymptotic_term n / (exp (-2) * nat_fac_to_real (n - 1))) =ᶠ[atTop]
        (fun n => (n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n)) := by
      filter_upwards [eventually_ge_atTop 3] with n hn
      exact asymp_term_ratio_eq n hn
    rw [tendsto_congr' h_eq]
    have h_lim_sum : Tendsto A258667_asymptotic_sum_part atTop (nhds 0) := tendsto_asymptotic_sum_part
    have h_lim : Tendsto (fun n : ℕ => (n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n)) atTop (nhds 1) := by
      have h_one : (1 : ℝ) = 1 * (1 + 0) := by ring
      conv_rhs => rw [h_one]
      apply Tendsto.mul
      · exact tendsto_n_div_n_sub_two
      · exact Tendsto.const_add 1 h_lim_sum
    exact h_lim



noncomputable def f_term (n k : ℕ) : ℝ :=
  if k < n then
    (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)
  else 0

noncomputable def g_term (k : ℕ) : ℝ :=
  ((-2 : ℝ)^k) / (Nat.factorial k : ℝ)

noncomputable def bound_term (k : ℕ) : ℝ :=
  (3 : ℝ)^k / (Nat.factorial k : ℝ)


lemma descFactorial_le_pow_mul_descFactorial (M D R : ℕ) (h : ∀ i < R, M - i ≤ 2 * (D - i)) :
    M.descFactorial R ≤ 2^R * D.descFactorial R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    have h_le_R : ∀ i < R, M - i ≤ 2 * (D - i) := by
      intro i hi
      exact h i (Nat.lt_succ_of_lt hi)
    have ih_inst := ih h_le_R
    have h_last := h R (Nat.lt_succ_self R)
    have h_step : M.descFactorial R * (M - R) ≤ (2^R * D.descFactorial R) * (2 * (D - R)) := by
      exact Nat.mul_le_mul ih_inst h_last
    have h_ring : (2^R * D.descFactorial R) * (2 * (D - R)) = 2^(R+1) * (D.descFactorial R * (D - R)) := by
      rw [pow_succ]
      ring
    rw [h_ring] at h_step
    rw [mul_comm (M - R), mul_comm (D - R)]
    exact h_step

lemma inner_term_step (n k j i : ℕ) (hj : j ≤ 4) (hi : i < k - j) :
    2 * n + j - (k + 10) - i ≤ 2 * (n - 1 - j - i) := by
  omega

lemma choose_mul_descFactorial_eq (n k j : ℕ) :
    Nat.choose (n - 1) j * k.descFactorial j = Nat.choose k j * (n - 1).descFactorial j := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose (n - 1) j]
  ring

lemma choose_factorial_le (n k j : ℕ) (hj : j ≤ 4) :
    Nat.choose (2 * n + j - (k + 10)) (k - j) * (k - j).factorial ≤ 2^(k - j) * (n - 1 - j).descFactorial (k - j) := by
  rw [mul_comm]
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  apply descFactorial_le_pow_mul_descFactorial
  intro i hi
  exact inner_term_step n k j i hj hi

lemma choose_bound_le_seven (j : ℕ) (hj : j ≤ 4) :
    Nat.choose (8 - j) j ≤ Nat.choose 7 j := by
  interval_cases j <;> decide

lemma algebra_identity (n k j : ℕ) (hj : j ≤ k) :
    Nat.choose (n - 1) j * (n - 1 - j).descFactorial (k - j) * k.descFactorial j =
    Nat.choose k j * (n - 1).descFactorial k := by
  have h_mul : Nat.choose (n - 1) j * (n - 1 - j).descFactorial (k - j) * k.descFactorial j =
      (Nat.choose (n - 1) j * k.descFactorial j) * (n - 1 - j).descFactorial (k - j) := by ring
  rw [h_mul, choose_mul_descFactorial_eq n k j]
  have h_assoc : Nat.choose k j * (n - 1).descFactorial j * (n - 1 - j).descFactorial (k - j) =
      Nat.choose k j * ((n - 1 - j).descFactorial (k - j) * (n - 1).descFactorial j) := by ring
  rw [h_assoc]
  have h_desc := Nat.descFactorial_mul_descFactorial (n := n - 1) (k := j) (m := k) hj
  rw [h_desc]

lemma term_by_term_bound (n k j : ℕ) (hj : j ≤ 4) (h_jk : j ≤ k) (hk : k < n) (hn : 8 ≤ n) :
    (Nat.choose (8 - j) j * Nat.choose (2 * n + j - (k + 10)) (k - j) : ℤ) * k.factorial ≤
    (Nat.choose k j * 2^(k - j) * (n - 1).descFactorial k : ℕ) := by
  have h_nat : Nat.choose (8 - j) j * Nat.choose (2 * n + j - (k + 10)) (k - j) * k.factorial ≤
      Nat.choose k j * 2^(k - j) * (n - 1).descFactorial k := by
    have hk_fac : k.factorial = (k - j).factorial * k.descFactorial j := by
      have := Nat.factorial_mul_descFactorial h_jk
      exact this.symm
    rw [hk_fac]
    have h_lhs : Nat.choose (8 - j) j * Nat.choose (2 * n + j - (k + 10)) (k - j) * ((k - j).factorial * k.descFactorial j) =
        (Nat.choose (8 - j) j * k.descFactorial j) * (Nat.choose (2 * n + j - (k + 10)) (k - j) * (k - j).factorial) := by ring
    rw [h_lhs]
    have h_f1 : Nat.choose (8 - j) j * k.descFactorial j ≤ Nat.choose (n - 1) j * k.descFactorial j := by
      apply Nat.mul_le_mul_right
      have h_seven : Nat.choose (8 - j) j ≤ Nat.choose 7 j := choose_bound_le_seven j hj
      have h_n_sub : Nat.choose 7 j ≤ Nat.choose (n - 1) j := by
        apply Nat.choose_le_choose
        omega
      exact h_seven.trans h_n_sub
    have h_f2 : Nat.choose (2 * n + j - (k + 10)) (k - j) * (k - j).factorial ≤ 2^(k - j) * (n - 1 - j).descFactorial (k - j) :=
      choose_factorial_le n k j hj
    have h_mul_le : (Nat.choose (8 - j) j * k.descFactorial j) * (Nat.choose (2 * n + j - (k + 10)) (k - j) * (k - j).factorial) ≤
        (Nat.choose (n - 1) j * k.descFactorial j) * (2^(k - j) * (n - 1 - j).descFactorial (k - j)) :=
      Nat.mul_le_mul h_f1 h_f2
    have h_rhs_rearrange : (Nat.choose (n - 1) j * k.descFactorial j) * (2^(k - j) * (n - 1 - j).descFactorial (k - j)) =
        2^(k - j) * (Nat.choose (n - 1) j * (n - 1 - j).descFactorial (k - j) * k.descFactorial j) := by ring
    rw [h_rhs_rearrange] at h_mul_le
    rw [algebra_identity n k j h_jk] at h_mul_le
    have h_final : 2 ^ (k - j) * (k.choose j * (n - 1).descFactorial k) = k.choose j * 2 ^ (k - j) * (n - 1).descFactorial k := by ring
    rw [h_final] at h_mul_le
    exact h_mul_le
  exact_mod_cast h_nat

lemma binomial_sum_three (k : ℕ) : ∑ j ∈ Finset.range (k + 1), k.choose j * 2 ^ (k - j) = 3 ^ k := by
  have h_add := add_pow (R := ℕ) 1 2 k
  simp only [one_pow, one_mul] at h_add
  rw [h_add]
  simp [mul_comm]

lemma descFactorial_ge_sub (n k : ℕ) (hk : 0 < k) (h_nk : k ≤ n) :
    n - k < n.descFactorial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Nat.descFactorial_succ]
    have h_pos : 0 < n.descFactorial k := by
      rw [Nat.descFactorial_pos]
      omega
    have h_ge1 : 1 ≤ n.descFactorial k := h_pos
    have h_step : n - k ≤ (n - k) * n.descFactorial k := by
      nth_rw 1 [← Nat.mul_one (n - k)]
      exact Nat.mul_le_mul_left (n - k) h_ge1
    have h_gt : n - (k + 1) < n - k := by omega
    exact h_gt.trans_le h_step

lemma ratio_linear_limit (A B : ℕ) : Tendsto (fun n : ℕ => (2 * (n : ℝ) - (A : ℝ)) / ((n : ℝ) - (B : ℝ))) atTop (nhds 2) := by
  have h_eq : (fun n : ℕ => (2 * (n : ℝ) - (A : ℝ)) / ((n : ℝ) - (B : ℝ))) =ᶠ[atTop] (fun n : ℕ => 2 + (2 * (B : ℝ) - (A : ℝ)) / ((n : ℝ) - (B : ℝ))) := by
    filter_upwards [eventually_ge_atTop (B + 1)] with n hn
    have h_pos : (n : ℝ) - (B : ℝ) ≠ 0 := by
      have : (n : ℝ) ≥ (B : ℝ) + 1 := by exact_mod_cast hn
      linarith
    field_simp
    ring
  rw [tendsto_congr' h_eq]
  have h_lim : Tendsto (fun n : ℕ => (2 * (B : ℝ) - (A : ℝ)) / ((n : ℝ) - (B : ℝ))) atTop (nhds 0) := by
    have h_div : (fun n : ℕ => (2 * (B : ℝ) - (A : ℝ)) / ((n : ℝ) - (B : ℝ))) = (fun n : ℕ => (2 * (B : ℝ) - (A : ℝ)) * (1 / ((n : ℝ) - (B : ℝ)))) := by
      ext n
      ring
    rw [h_div]
    have h_zero : (0 : ℝ) = (2 * (B : ℝ) - (A : ℝ)) * 0 := by ring
    rw [h_zero]
    apply Tendsto.const_mul
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 2 / (n : ℝ)) ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · have h_eq2 : (fun (n : ℕ) => 2 / (n : ℝ)) = (fun (n : ℕ) => (1 / (n : ℝ)) * 2) := by
        ext n
        ring
      rw [h_eq2]
      have h_zero2 : (0 : ℝ) = 0 * 2 := by ring
      rw [h_zero2]
      exact Tendsto.mul_const 2 tendsto_one_div_atTop_nhds_zero_nat
    · filter_upwards [eventually_ge_atTop (B + 1)] with n hn
      have h_pos : (n : ℝ) - (B : ℝ) > 0 := by
        have h_gt : B < n := by omega
        have : (B : ℝ) < (n : ℝ) := by exact_mod_cast h_gt
        linarith
      exact div_nonneg (by linarith) h_pos.le
    · filter_upwards [eventually_ge_atTop (2 * B + 2)] with n hn
      have h_pos : (n : ℝ) - (B : ℝ) > 0 := by
        have h_gt : B < n := by omega
        have : (B : ℝ) < (n : ℝ) := by exact_mod_cast h_gt
        linarith
      have h_pos_n : (n : ℝ) > 0 := by
        have : 0 < n := by omega
        exact_mod_cast this
      rw [div_le_div_iff₀ h_pos h_pos_n]
      have : (n : ℝ) ≥ 2 * (B : ℝ) := by
        have h_ge : 2 * B ≤ n := by omega
        exact_mod_cast h_ge
      linarith
  have h_two : (2 : ℝ) = 2 + 0 := by ring
  conv_rhs => rw [h_two]
  exact Tendsto.const_add 2 h_lim

lemma limit_j_pos (k j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (hjk : j ≤ k) :
    Tendsto (fun (n : ℕ) => (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (n - 1).descFactorial k) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ))
      (h := fun (n : ℕ) => (2^(k-j) / (k-j).factorial : ℝ) / ((n : ℝ) - (j : ℝ))) ?_ ?_ ?_ ?_
  · exact tendsto_const_nhds
  · have h_div : (fun (n : ℕ) => (2^(k-j) / (k-j).factorial : ℝ) / ((n : ℝ) - (j : ℝ))) = (fun (n : ℕ) => (2^(k-j) / (k-j).factorial : ℝ) * (1 / ((n : ℝ) - (j : ℝ)))) := by
      ext n
      ring
    rw [h_div]
    have h_zero : (0 : ℝ) = (2^(k-j) / (k-j).factorial : ℝ) * 0 := by ring
    rw [h_zero]
    apply Tendsto.const_mul
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (_ : ℕ) => (0 : ℝ)) (h := fun (n : ℕ) => 2 / (n : ℝ)) ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · have h_eq2 : (fun (n : ℕ) => 2 / (n : ℝ)) = (fun (n : ℕ) => (1 / (n : ℝ)) * 2) := by
        ext n
        ring
      rw [h_eq2]
      have h_zero2 : (0 : ℝ) = 0 * 2 := by ring
      rw [h_zero2]
      exact Tendsto.mul_const 2 tendsto_one_div_atTop_nhds_zero_nat
    · filter_upwards [eventually_ge_atTop (j + 1)] with n hn
      have h_pos : (n : ℝ) - (j : ℝ) > 0 := by
        have h_gt : j < n := by omega
        have : (j : ℝ) < (n : ℝ) := by exact_mod_cast h_gt
        linarith
      exact div_nonneg (by linarith) h_pos.le
    · filter_upwards [eventually_ge_atTop (2 * j + 2)] with n hn
      have h_pos : (n : ℝ) - (j : ℝ) > 0 := by
        have h_gt : j < n := by omega
        have : (j : ℝ) < (n : ℝ) := by exact_mod_cast h_gt
        linarith
      have h_pos_n : (n : ℝ) > 0 := by
        have : 0 < n := by omega
        exact_mod_cast this
      rw [div_le_div_iff₀ h_pos h_pos_n]
      have : (n : ℝ) ≥ 2 * (j : ℝ) := by
        have h_ge : 2 * j ≤ n := by omega
        exact_mod_cast h_ge
      linarith
  · filter_upwards [eventually_ge_atTop (k + 10)] with n hn
    have h_desc_pos : 0 < ((n - 1).descFactorial k : ℝ) := by
      have : 0 < (n - 1).descFactorial k := by
        rw [Nat.descFactorial_pos]
        omega
      exact_mod_cast this
    exact div_nonneg (by positivity) h_desc_pos.le
  · filter_upwards [eventually_ge_atTop (k + 10)] with n hn
    have h_desc_pos : 0 < ((n - 1).descFactorial k : ℝ) := by
      have : 0 < (n - 1).descFactorial k := by
        rw [Nat.descFactorial_pos]
        omega
      exact_mod_cast this
    rw [div_le_iff₀ h_desc_pos]
    have h_pos : (n : ℝ) - (j : ℝ) > 0 := by
      have h_gt : j < n := by omega
      have : (j : ℝ) < (n : ℝ) := by exact_mod_cast h_gt
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h_pos]
    have h_desc_split : ((n - 1).descFactorial k : ℝ) = ((n - 1).descFactorial j : ℝ) * ((n - 1 - j).descFactorial (k - j) : ℝ) := by
      have h_split := Nat.descFactorial_mul_descFactorial (n := n - 1) (k := j) (m := k) hjk
      rw [mul_comm] at h_split
      exact_mod_cast h_split.symm
    rw [h_desc_split]
    have h_fac_pos : 0 < ((k - j).factorial : ℝ) := by
      have : 0 < (k - j).factorial := Nat.factorial_pos _
      exact_mod_cast this
    have h_le_step : (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) * ((n : ℝ) - (j : ℝ)) * (k - j).factorial ≤
        (2 ^ (k - j) : ℝ) * ((n - 1 - j).descFactorial (k - j) : ℝ) * ((n - 1).descFactorial j : ℝ) := by
      have h_fac_le : (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) * (k - j).factorial ≤ (2 ^ (k - j) : ℝ) * ((n - 1 - j).descFactorial (k - j) : ℝ) := by
        have h_nat_le := choose_factorial_le n k j hj4
        exact_mod_cast h_nat_le
      have h_desc_ge : ((n : ℝ) - (j : ℝ)) ≤ ((n - 1).descFactorial j : ℝ) := by
        have h_ge_nat : n - j ≤ (n - 1).descFactorial j := by
          have := descFactorial_ge_sub (n - 1) j hj (by omega)
          omega
        rw [← Nat.cast_sub (show j ≤ n by omega)]
        exact_mod_cast h_ge_nat
      have h_rhs_nonneg : 0 ≤ (2 ^ (k - j) : ℝ) * ((n - 1 - j).descFactorial (k - j) : ℝ) := by positivity
      have h_mul := mul_le_mul h_fac_le h_desc_ge (by positivity) h_rhs_nonneg
      linarith
    have h_rw : (2 ^ (k - j) : ℝ) / ((k - j).factorial : ℝ) * (((n - 1).descFactorial j : ℝ) * ((n - 1 - j).descFactorial (k - j) : ℝ)) =
                ((2 ^ (k - j) : ℝ) * ((n - 1 - j).descFactorial (k - j) : ℝ) * ((n - 1).descFactorial j : ℝ)) / ((k - j).factorial : ℝ) := by ring
    rw [h_rw]
    rw [le_div_iff₀ h_fac_pos]
    linarith [h_le_step]

lemma limit_j_zero (k : ℕ) :
    Tendsto (fun n => ((2 * n - (k + 10)).descFactorial k : ℝ) / (n - 1).descFactorial k) atTop (nhds (2^k)) := by
  have h_eq : (fun n => ((2 * n - (k + 10)).descFactorial k : ℝ) / (n - 1).descFactorial k) =ᶠ[atTop]
      (fun (n : ℕ) => ∏ i ∈ Finset.range k, ((2 * (n : ℝ) - ((k + 10 + i : ℕ) : ℝ)) / ((n : ℝ) - ((1 + i : ℕ) : ℝ)))) := by
    filter_upwards [eventually_ge_atTop (k + 10)] with n hn
    have h_desc1 : ((2 * n - (k + 10)).descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((2 * n - (k + 10) - i : ℕ) : ℝ) := by
      push_cast
      exact_mod_cast Nat.descFactorial_eq_prod_range (2 * n - (k + 10)) k
    have h_desc2 : ((n - 1).descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((n - 1 - i : ℕ) : ℝ) := by
      push_cast
      exact_mod_cast Nat.descFactorial_eq_prod_range (n - 1) k
    rw [h_desc1, h_desc2, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h_sub1 : 2 * n - (k + 10) - i = 2 * n - (k + 10 + i) := by omega
    have h_sub2 : n - 1 - i = n - (1 + i) := by omega
    rw [h_sub1, h_sub2]
    have h_le1 : k + 10 + i ≤ 2 * n := by omega
    have h_le2 : 1 + i ≤ n := by omega
    rw [Nat.cast_sub h_le1, Nat.cast_sub h_le2]
    push_cast
    rfl
  rw [tendsto_congr' h_eq]
  have h_prod : Tendsto (fun (n : ℕ) => ∏ i ∈ Finset.range k, ((2 * (n : ℝ) - ((k + 10 + i : ℕ) : ℝ)) / ((n : ℝ) - ((1 + i : ℕ) : ℝ)))) atTop
      (nhds (∏ i ∈ Finset.range k, (2 : ℝ))) := by
    apply tendsto_finset_prod
    intro i hi
    exact ratio_linear_limit (k + 10 + i) (1 + i)
  have h_two_pow : (∏ i ∈ Finset.range k, (2 : ℝ)) = (2^k : ℝ) := by
    simp
  rw [h_two_pow] at h_prod
  exact h_prod

lemma inner_sum_split_limit (k : ℕ) :
    Tendsto (fun n => (A258667_inner_sum n k : ℝ) / (n - 1).descFactorial k) atTop (nhds (2^k / k.factorial)) := by
  have h_eq : (fun n => (A258667_inner_sum n k : ℝ) / (n - 1).descFactorial k) =ᶠ[atTop]
      (fun n => ((Nat.choose 8 0 * Nat.choose (2 * n - (k + 10)) k : ℤ) : ℝ) / (n - 1).descFactorial k +
                ∑ j ∈ Finset.Icc 1 (min k 4), ((Nat.choose (8 - j) j * Nat.choose (2 * n + j - (k + 10)) (k - j) : ℤ) : ℝ) / (n - 1).descFactorial k) := by
    filter_upwards [eventually_ge_atTop (k + 5)] with n hn
    unfold A258667_inner_sum
    dsimp only
    have h_L : max 0 (k + 5 - n) = 0 := by omega
    rw [h_L]
    have h_split : Finset.Icc 0 (min k 4) = insert 0 (Finset.Icc 1 (min k 4)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h_split, Finset.sum_insert (by simp)]
    push_cast
    rw [add_div]
    congr 2
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [tendsto_congr' h_eq]
  have h_zero : (2^k / k.factorial : ℝ) = (2^k / k.factorial : ℝ) + 0 := by ring
  conv_rhs => rw [h_zero]
  apply Tendsto.add
  · have h_ratio : (fun n => ((Nat.choose 8 0 * Nat.choose (2 * n - (k + 10)) k : ℤ) : ℝ) / (n - 1).descFactorial k) =
        (fun n => ((2 * n - (k + 10)).descFactorial k : ℝ) / (n - 1).descFactorial k / k.factorial) := by
      ext n
      have h_choose_eq : (Nat.choose (2 * n - (k + 10)) k : ℝ) = ((2 * n - (k + 10)).descFactorial k : ℝ) / (k.factorial : ℝ) := by
        have h_mul : (Nat.choose (2 * n - (k + 10)) k : ℝ) * (k.factorial : ℝ) = ((2 * n - (k + 10)).descFactorial k : ℝ) := by
          have h_nat : Nat.choose (2 * n - (k + 10)) k * k.factorial = (2 * n - (k + 10)).descFactorial k := by
            have h_eq := Nat.descFactorial_eq_factorial_mul_choose (2 * n - (k + 10)) k
            rw [mul_comm]
            exact h_eq.symm
          exact_mod_cast h_nat
        have h_fac_ne : (k.factorial : ℝ) ≠ 0 := by positivity
        rw [← h_mul, mul_div_cancel_right₀ _ h_fac_ne]
      simp [h_choose_eq]
      ring
    rw [h_ratio]
    have h_lim := limit_j_zero k
    exact Tendsto.div_const h_lim _
  · have h_ratio : (fun n => ∑ j ∈ Finset.Icc 1 (min k 4), ((Nat.choose (8 - j) j * Nat.choose (2 * n + j - (k + 10)) (k - j) : ℤ) : ℝ) / (n - 1).descFactorial k) =
        (fun n => ∑ j ∈ Finset.Icc 1 (min k 4), (Nat.choose (8 - j) j : ℝ) * ((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (n - 1).descFactorial k)) := by
      ext n
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
    rw [h_ratio]
    have h_zero_sum : (0 : ℝ) = ∑ j ∈ Finset.Icc 1 (min k 4), (0 : ℝ) := by simp
    rw [h_zero_sum]
    apply tendsto_finset_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := hj.1
    have hj4 : j ≤ 4 := by
      have : min k 4 ≤ 4 := min_le_right _ _
      omega
    have hjk : j ≤ k := by
      have : min k 4 ≤ k := min_le_left _ _
      omega
    have h_pos_lim := limit_j_pos k j hj1 hj4 hjk
    have h_mul := Tendsto.const_mul (Nat.choose (8 - j) j : ℝ) h_pos_lim
    rw [mul_zero] at h_mul
    exact h_mul

lemma f_term_pointwise (k : ℕ) : Tendsto (fun n ↦ f_term n k) atTop (nhds (g_term k)) := by
  have h_eventually : (fun n => f_term n k) =ᶠ[atTop] (fun n => (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)) := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    unfold f_term
    have : k < n := hn
    simp [this]
  rw [tendsto_congr' h_eventually]
  have h_mul_eq : (fun n => (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)) =
      (fun n => ((-1 : ℝ)^k) * ((A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ))) := by
    ext n
    ring
  rw [h_mul_eq]
  have h_lim := inner_sum_split_limit k
  have h_mul_lim := Tendsto.const_mul ((-1 : ℝ)^k) h_lim
  have h_g_eq : ((-1 : ℝ)^k) * (2^k / k.factorial) = g_term k := by
    unfold g_term
    have h_pow : ((-1 : ℝ)^k) * (2^k) = ((-2 : ℝ)^k) := by
      rw [← mul_pow]
      ring
    calc ((-1 : ℝ)^k) * (2^k / k.factorial)
      _ = (((-1 : ℝ)^k) * 2^k) / k.factorial := by ring
      _ = ((-2 : ℝ)^k) / k.factorial := by rw [h_pow]
  rw [h_g_eq] at h_mul_lim
  exact h_mul_lim

lemma inner_sum_mul_factorial_le (n k : ℕ) (hk : k < n) (hn : 8 ≤ n) :
    A258667_inner_sum n k * (k.factorial : ℤ) ≤ ((3 ^ k * (n - 1).descFactorial k : ℕ) : ℤ) := by
  unfold A258667_inner_sum
  rw [Finset.sum_mul]
  have h_le : ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
      (let term1 := Nat.choose (8 - j) j
       let term2 := Nat.choose (2 * n + j - (k + 10)) (k - j)
       Int.ofNat term1 * Int.ofNat term2 : ℤ) * k.factorial ≤
      ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
      ((Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k : ℕ) : ℤ) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj4 : j ≤ 4 := by
      have : min k 4 ≤ 4 := min_le_right _ _
      omega
    have h_jk : j ≤ k := by
      have : min k 4 ≤ k := min_le_left _ _
      omega
    exact term_by_term_bound n k j hj4 h_jk hk hn
  have h_nat_le : ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
      Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k ≤
      ∑ j ∈ Finset.range (k + 1),
      Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k := by
    have h_subset : Finset.Icc (max 0 (k + 5 - n)) (min k 4) ⊆ Finset.range (k + 1) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      have : min k 4 ≤ k := min_le_left _ _
      omega
    apply Finset.sum_le_sum_of_subset h_subset
  have h_sum_le : ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
      ((Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k : ℕ) : ℤ) ≤
      ∑ j ∈ Finset.range (k + 1),
      ((Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k : ℕ) : ℤ) := by
    exact_mod_cast h_nat_le
  have h_sum_eq : ∑ j ∈ Finset.range (k + 1), ((Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k : ℕ) : ℤ) =
      ((3 ^ k * (n - 1).descFactorial k : ℕ) : ℤ) := by
    have h_factor : ∑ j ∈ Finset.range (k + 1), ((Nat.choose k j * 2 ^ (k - j) * (n - 1).descFactorial k : ℕ) : ℤ) =
        (∑ j ∈ Finset.range (k + 1), (Nat.choose k j * 2 ^ (k - j) : ℤ)) * ((n - 1).descFactorial k : ℤ) := by
      push_cast
      rw [← Finset.sum_mul]
    rw [h_factor]
    have h_bin : (∑ j ∈ Finset.range (k + 1), (Nat.choose k j * 2 ^ (k - j) : ℤ)) = (3 ^ k : ℤ) := by
      exact_mod_cast binomial_sum_three k
    rw [h_bin]
    push_cast
    ring
  linarith

lemma inner_sum_nonneg (n k : ℕ) : 0 ≤ A258667_inner_sum n k := by
  unfold A258667_inner_sum
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg <;> exact Int.natCast_nonneg _

lemma f_term_bound (n k : ℕ) (hn : 8 ≤ n) : |f_term n k| ≤ bound_term k := by
  unfold f_term bound_term
  split_ifs with hk
  · -- Case k < n
    have h_abs : |(((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)| = (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ) := by
      rw [abs_mul]
      have h_sign_abs : |(-1 : ℝ)^k| = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      have h_desc_pos : 0 < (Nat.descFactorial (n - 1) k : ℝ) := by
        have : 0 < Nat.descFactorial (n - 1) k := by
          rw [Nat.descFactorial_pos]
          omega
        exact_mod_cast this
      rw [abs_div, h_sign_abs, abs_of_pos h_desc_pos]
      have h_inner_pos : 0 ≤ (A258667_inner_sum n k : ℝ) := by
        exact_mod_cast inner_sum_nonneg n k
      rw [abs_of_nonneg h_inner_pos]
      ring
    rw [h_abs]
    have h_div_le : (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ) ≤ (3 : ℝ)^k / (Nat.factorial k : ℝ) := by
      have h_desc_pos : 0 < (Nat.descFactorial (n - 1) k : ℝ) := by
        have : 0 < Nat.descFactorial (n - 1) k := by
          rw [Nat.descFactorial_pos]
          omega
        exact_mod_cast this
      have h_fac_pos : 0 < (Nat.factorial k : ℝ) := by
        have : 0 < Nat.factorial k := Nat.factorial_pos k
        exact_mod_cast this
      rw [div_le_div_iff₀ h_desc_pos h_fac_pos]
      have h_int_le := inner_sum_mul_factorial_le n k hk hn
      have h_cast : ((A258667_inner_sum n k * (k.factorial : ℤ) : ℤ) : ℝ) ≤ (((3 ^ k * (n - 1).descFactorial k : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast h_int_le
      push_cast at h_cast
      linarith
    exact h_div_le
  · -- Case k >= n
    simp
    positivity

lemma f_term_bound_eventually : ∀ᶠ n in atTop, ∀ k, ‖f_term n k‖ ≤ bound_term k := by
  filter_upwards [eventually_ge_atTop 8] with n hn k
  exact f_term_bound n k hn

lemma summable_bound_term : Summable bound_term := by
  unfold bound_term
  exact Real.summable_pow_div_factorial 3



lemma f_term_tsum_eq_sum (n : ℕ) :
    ∑' k, f_term n k = ∑ k ∈ Finset.range n, (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ) := by
  have h_eq : (∑' k, f_term n k) = ∑ k ∈ Finset.range n, f_term n k := by
    apply tsum_eq_sum
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    unfold f_term
    simp [hk]
  rw [h_eq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  unfold f_term
  simp [hk]

lemma g_term_tsum_eq_exp : ∑' k, g_term k = exp (-2) := by
  have h_sum := NormedSpace.expSeries_div_hasSum_exp (-2 : ℝ)
  have h_g : g_term = (fun k => (-2 : ℝ)^k / (Nat.factorial k : ℝ)) := by
    ext k
    unfold g_term
    rfl
  rw [h_g]
  have h_exp : NormedSpace.exp (-2 : ℝ) = exp (-2) := by
    rw [← Real.exp_eq_exp_ℝ]
  rw [← h_exp]
  exact h_sum.tsum_eq


lemma tendsto_f_term_tsum : Tendsto (fun n ↦ ∑' k, f_term n k) atTop (nhds (exp (-2))) := by
  have h_conv := tendsto_tsum_of_dominated_convergence (G := ℝ) (f := f_term) (g := g_term) (bound := bound_term)
    summable_bound_term f_term_pointwise f_term_bound_eventually
  rw [g_term_tsum_eq_exp] at h_conv
  exact h_conv

lemma h2_proof_helper : Tendsto (fun n => |∑ k ∈ Finset.range n, (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)| / exp (-2)) atTop (nhds 1) := by
  have h_eq : (fun n => |∑ k ∈ Finset.range n, (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)| / exp (-2)) =
      (fun n => |∑' k, f_term n k| / exp (-2)) := by
    ext n
    rw [f_term_tsum_eq_sum n]
  rw [h_eq]
  have h_exp_pos : exp (-2) > 0 := exp_pos (-2)
  have h_limit : Tendsto (fun n => |∑' k, f_term n k| / exp (-2)) atTop (nhds (|exp (-2)| / exp (-2))) := by
    apply Tendsto.div_const
    apply Tendsto.abs
    exact tendsto_f_term_tsum
  have h_one : |exp (-2)| / exp (-2) = 1 := by
    rw [abs_of_pos h_exp_pos, div_self (ne_of_gt h_exp_pos)]
  rw [h_one] at h_limit
  exact h_limit


theorem oeis_A258667_conjecture_0 :
  IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) A258667_asymptotic_term := by
  have h2_proof : IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
    refine isEquivalent_of_tendsto_one' ?_ ?_
    · intro n hn
      have h_exp : exp (-2) > 0 := exp_pos (-2)
      have h_fac : nat_fac_to_real (n - 1) > 0 := by
        unfold nat_fac_to_real
        positivity
      have h_pos : exp (-2) * nat_fac_to_real (n - 1) > 0 := mul_pos h_exp h_fac
      linarith
    · change Tendsto (fun n => (A258667 n : ℝ) / (exp (-2) * nat_fac_to_real (n - 1))) atTop (nhds 1)
      have h_eq : (fun n => (A258667 n : ℝ) / (exp (-2) * nat_fac_to_real (n - 1))) =ᶠ[atTop]
          (fun n => |∑ k ∈ Finset.range n, (((-1 : ℝ)^k) / (Nat.descFactorial (n - 1) k : ℝ)) * (A258667_inner_sum n k : ℝ)| / exp (-2)) := by
        filter_upwards [eventually_ge_atTop 6] with n hn
        have h_formula := A258667_formula n hn
        rw [h_formula]
        have h_fac_ne : nat_fac_to_real (n - 1) ≠ 0 := by
          unfold nat_fac_to_real
          positivity
        field_simp
      rw [tendsto_congr' h_eq]
      exact h2_proof_helper
  exact IsEquivalent.trans h2_proof h1_proof.symm
