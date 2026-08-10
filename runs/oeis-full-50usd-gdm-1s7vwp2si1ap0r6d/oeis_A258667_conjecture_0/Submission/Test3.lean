import FormalConjectures.Util.ProblemImports

open BigOperators Nat Int Real Asymptotics Filter

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

-- We need `tendsto_asymptotic_sum_part` for `tendsto_asymptotic_term_ratio`.
-- Since we don't have it in Test3.lean, we will define a sorry for now just to test the logic, or we can copy it from Spec.lean if we want to compile.
-- Actually we can just write the logic of tendsto_asymptotic_term_ratio with sorry first.
lemma tendsto_asymptotic_term_ratio (h_sum : Tendsto A258667_asymptotic_sum_part atTop (nhds 0)) :
    Tendsto (fun n => A258667_asymptotic_term n / (exp (-2) * nat_fac_to_real (n - 1))) atTop (nhds 1) := by
  have h_eq : (fun n => A258667_asymptotic_term n / (exp (-2) * nat_fac_to_real (n - 1))) =ᶠ[atTop] (fun n => (n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n)) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact asymp_term_ratio_eq n hn
  rw [tendsto_congr' h_eq]
  have h_one : (1 : ℝ) = 1 * (1 + 0) := by ring
  conv_rhs => rw [h_one]
  apply Tendsto.mul
  · exact tendsto_n_div_n_sub_two
  · exact Tendsto.const_add 1 h_sum

private def A258667_inner_sum (n k : ℕ) : ℤ :=
  let L : ℕ := max 0 (k + 5 - n)
  let U : ℕ := min k 4
  Finset.sum (Finset.Icc L U) fun j =>
    let term1 := Nat.choose (8 - j) j
    let term2 := Nat.choose (2 * n + j - (k + 10)) (k - j)
    ofNat term1 * ofNat term2

def A258667 (n : ℕ) : ℕ :=
  if h : n ≤ 5 then 0 else
  (Finset.sum (Finset.range n) fun k =>
    let sign : ℤ := if k % 2 = 0 then 1 else -1
    let fac_term : ℤ := ofNat (Nat.factorial (n - 1 - k))
    sign * fac_term * A258667_inner_sum n k
  ).natAbs

lemma h_abs_test (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

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
  push_cast
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

lemma tendsto_denom (h_sum : Tendsto A258667_asymptotic_sum_part atTop (nhds 0)) :
    Tendsto (fun n : ℕ => exp (-2) * (((n : ℝ) / (n - 2 : ℝ)) * (1 + A258667_asymptotic_sum_part n))) atTop (nhds (exp (-2))) := by
  have h_one : (exp (-2) : ℝ) = exp (-2) * (1 * (1 + 0)) := by ring
  conv_rhs => rw [h_one]
  apply Tendsto.const_mul
  apply Tendsto.mul
  · exact tendsto_n_div_n_sub_two
  · exact Tendsto.const_add 1 h_sum

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
    have h_lim : Tendsto (fun n => (n : ℝ) / (n - 2 : ℝ) * (1 + A258667_asymptotic_sum_part n)) atTop (nhds 1) := by
      have h_one : (1 : ℝ) = 1 * (1 + 0) := by ring
      conv_rhs => rw [h_one]
      apply Tendsto.mul
      · exact tendsto_n_div_n_sub_two
      · exact Tendsto.const_add 1 h_lim_sum
    exact h_lim

