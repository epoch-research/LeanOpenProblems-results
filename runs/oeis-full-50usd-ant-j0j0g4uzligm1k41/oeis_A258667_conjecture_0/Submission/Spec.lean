import FormalConjectures.Util.ProblemImports

open BigOperators Nat Int Real Asymptotics Filter Topology Finset

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


/-- Core asymptotic: `C(2n-t, m) / n^m → 2^m / m!`. -/
lemma core_div_eq (t m : ℕ) :
    Tendsto (fun n : ℕ => (Nat.choose (2 * n - t) m : ℝ) / (n : ℝ) ^ m) atTop
      (𝓝 ((2 : ℝ) ^ m / (m ! : ℝ))) := by
  have hfac : ∀ i ∈ Finset.range m,
      Tendsto (fun n : ℕ => (2 : ℝ) - ((t + i : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 2) := by
    intro i _
    have h0 : Tendsto (fun n : ℕ => ((t + i : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub h0
  have hprod : Tendsto
      (fun n : ℕ => ∏ i ∈ Finset.range m, ((2 : ℝ) - ((t + i : ℕ) : ℝ) / (n : ℝ))) atTop
      (𝓝 (∏ _i ∈ Finset.range m, (2 : ℝ))) := tendsto_finset_prod _ hfac
  rw [Finset.prod_const, Finset.card_range] at hprod
  have hlim : Tendsto
      (fun n : ℕ => (m ! : ℝ)⁻¹ * ∏ i ∈ Finset.range m, ((2 : ℝ) - ((t + i : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 ((m ! : ℝ)⁻¹ * (2 : ℝ) ^ m)) :=
    hprod.const_mul _
  have heq : (fun n : ℕ => (m ! : ℝ)⁻¹ * ∏ i ∈ Finset.range m, ((2 : ℝ) - ((t + i : ℕ) : ℝ) / (n : ℝ)))
      =ᶠ[atTop] (fun n : ℕ => (Nat.choose (2 * n - t) m : ℝ) / (n : ℝ) ^ m) := by
    filter_upwards [eventually_ge_atTop (t + m), eventually_gt_atTop 0] with n hn hn0
    have hn0' : (n : ℝ) ≠ 0 := by positivity
    have hd : ((Nat.descFactorial (2 * n - t) m : ℕ) : ℝ)
        = ∏ i ∈ Finset.range m, (2 * (n : ℝ) - ((t + i : ℕ) : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range]
      push_cast
      apply Finset.prod_congr rfl
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have hcc : ((2 * n - t - i : ℕ) : ℝ) = 2 * (n : ℝ) - (t : ℝ) - (i : ℝ) := by
        push_cast [Nat.cast_sub (by omega : t ≤ 2 * n), Nat.cast_sub (by omega : i ≤ 2 * n - t)]
        ring
      push_cast at hcc ⊢
      linarith [hcc]
    have hchoose : (Nat.choose (2 * n - t) m : ℝ)
        = ((Nat.descFactorial (2 * n - t) m : ℕ) : ℝ) / (m ! : ℝ) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      field_simp
    rw [hchoose, hd]
    have hfac2 : ∀ i ∈ Finset.range m,
        (2 : ℝ) - ((t + i : ℕ) : ℝ) / (n : ℝ) = (2 * (n : ℝ) - ((t + i : ℕ) : ℝ)) / (n : ℝ) := by
      intro i _; field_simp
    rw [Finset.prod_congr rfl hfac2, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    field_simp
  rw [show (2 : ℝ) ^ m / (m ! : ℝ) = (m ! : ℝ)⁻¹ * (2 : ℝ) ^ m by ring]
  exact hlim.congr' heq

/-- For `m < p`, `C(2n-t, m) / n^p → 0`. -/
lemma core_div_pow (t m p : ℕ) (hmp : m < p) :
    Tendsto (fun n : ℕ => (Nat.choose (2 * n - t) m : ℝ) / (n : ℝ) ^ p) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ (p - m))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) ^ (p - m)) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop
  have hmul := (core_div_eq t m).mul hinv
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hn0' : (n : ℝ) ≠ 0 := by positivity
  have hpe : (n : ℝ) ^ p = (n : ℝ) ^ m * (n : ℝ) ^ (p - m) := by
    rw [← pow_add]; congr 1; omega
  rw [hpe]; field_simp

/-- Limit of a single inner-sum term divided by `n^k`. -/
lemma term_limit (k j : ℕ) (hj : j ≤ min k 4) :
    Tendsto (fun n : ℕ => (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (n : ℝ) ^ k) atTop
      (𝓝 (if j = 0 then (2 : ℝ) ^ k / (k ! : ℝ) else 0)) := by
  have hjk : j ≤ k := le_trans hj (min_le_left _ _)
  have hcongr : (fun n : ℕ => (Nat.choose (2 * n - (k + 10 - j)) (k - j) : ℝ) / (n : ℝ) ^ k)
      =ᶠ[atTop] (fun n : ℕ => (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (n : ℝ) ^ k) := by
    filter_upwards [eventually_ge_atTop (k + 10)] with n hn
    have : 2 * n + j - (k + 10) = 2 * n - (k + 10 - j) := by omega
    rw [this]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [Nat.sub_zero, Nat.add_zero, if_true]
    exact core_div_eq (k + 10) k
  · rw [if_neg hj0]
    have hmlt : k - j < k := by omega
    have h := core_div_pow (k + 10 - j) (k - j) k hmlt
    exact h.congr' hcongr

/-- inner-sum divided by `n^k` tends to `2^k/k!`. -/
lemma inner_sum_div_limit (k : ℕ) :
    Tendsto (fun n : ℕ => (A258667_inner_sum n k : ℝ) / (n : ℝ) ^ k) atTop
      (𝓝 ((2 : ℝ) ^ k / (k ! : ℝ))) := by
  set s : Finset ℕ := Finset.Icc 0 (min k 4) with hs
  -- the per-term tendsto
  have hterm : ∀ j ∈ s,
      Tendsto (fun n : ℕ => (Nat.choose (8 - j) j : ℝ) *
        ((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (n : ℝ) ^ k)) atTop
        (𝓝 ((Nat.choose (8 - j) j : ℝ) * (if j = 0 then (2 : ℝ) ^ k / (k ! : ℝ) else 0))) := by
    intro j hj
    have hjs : j ≤ min k 4 := by
      simp only [hs, Finset.mem_Icc] at hj; exact hj.2
    exact (term_limit k j hjs).const_mul _
  have hsum := tendsto_finset_sum s hterm
  -- evaluate the limiting sum
  have hval : (∑ j ∈ s, (Nat.choose (8 - j) j : ℝ) * (if j = 0 then (2 : ℝ) ^ k / (k ! : ℝ) else 0))
      = (2 : ℝ) ^ k / (k ! : ℝ) := by
    rw [Finset.sum_eq_single_of_mem 0]
    · simp
    · simp [hs, Finset.mem_Icc]
    · intro b _ hb; simp [hb]
  rw [hval] at hsum
  -- now relate the actual function to the sum, eventually
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (k + 5), eventually_gt_atTop 0] with n hn hn0
  have hL : max 0 (k + 5 - n) = 0 := by omega
  show (∑ j ∈ s, (Nat.choose (8 - j) j : ℝ) *
      ((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (n : ℝ) ^ k))
      = (A258667_inner_sum n k : ℝ) / (n : ℝ) ^ k
  rw [A258667_inner_sum]
  simp only [hL, hs, Int.ofNat_eq_natCast]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- `descFactorial(n-1, k) / n^k → 1`. -/
lemma descFactorial_div_limit (k : ℕ) :
    Tendsto (fun n : ℕ => (Nat.descFactorial (n - 1) k : ℝ) / (n : ℝ) ^ k) atTop (𝓝 1) := by
  have hfac : ∀ i ∈ Finset.range k,
      Tendsto (fun n : ℕ => (1 : ℝ) - ((i + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    intro i _
    have h0 : Tendsto (fun n : ℕ => ((i + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have hprod : Tendsto
      (fun n : ℕ => ∏ i ∈ Finset.range k, ((1 : ℝ) - ((i + 1 : ℕ) : ℝ) / (n : ℝ))) atTop
      (𝓝 (∏ _i ∈ Finset.range k, (1 : ℝ))) := tendsto_finset_prod _ hfac
  rw [Finset.prod_const_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (k + 1), eventually_gt_atTop 0] with n hn hn0
  have hn0' : (n : ℝ) ≠ 0 := by positivity
  have hd : ((Nat.descFactorial (n - 1) k : ℕ) : ℝ)
      = ∏ i ∈ Finset.range k, ((n : ℝ) - ((i + 1 : ℕ) : ℝ)) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have hcc : ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : i ≤ n - 1)]
      ring
    push_cast at hcc ⊢
    linarith [hcc]
  have hfac2 : ∀ i ∈ Finset.range k,
      (1 : ℝ) - ((i + 1 : ℕ) : ℝ) / (n : ℝ) = ((n : ℝ) - ((i + 1 : ℕ) : ℝ)) / (n : ℝ) := by
    intro i _; field_simp
  rw [Finset.prod_congr rfl hfac2, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range, ← hd]

/-- the term function for Tannery's theorem. -/
noncomputable def F (n k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) * (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ)

/-- per-`k` limit of `F n k`. -/
lemma F_limit (k : ℕ) :
    Tendsto (fun n : ℕ => F n k) atTop (𝓝 ((-2 : ℝ) ^ k / (k ! : ℝ))) := by
  have hdiv : Tendsto (fun n : ℕ => ((A258667_inner_sum n k : ℝ) / (n : ℝ) ^ k) /
      ((Nat.descFactorial (n - 1) k : ℝ) / (n : ℝ) ^ k)) atTop
      (𝓝 (((2 : ℝ) ^ k / (k ! : ℝ)) / 1)) :=
    (inner_sum_div_limit k).div (descFactorial_div_limit k) (by norm_num)
  rw [div_one] at hdiv
  have hmul := hdiv.const_mul ((-1 : ℝ) ^ k)
  have hval : (-1 : ℝ) ^ k * ((2 : ℝ) ^ k / (k ! : ℝ)) = (-2 : ℝ) ^ k / (k ! : ℝ) := by
    rw [← neg_one_mul (2 : ℝ), mul_pow]; ring
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hn0' : (n : ℝ) ^ k ≠ 0 := by positivity
  rw [F, div_div_div_cancel_right₀]
  · ring
  · exact hn0'

/-- monotonicity of descending factorial in the lower index. -/
lemma descFactorial_mono_right (a m k : ℕ) (hmk : m ≤ k) (hk : k ≤ a) :
    Nat.descFactorial a m ≤ Nat.descFactorial a k := by
  have e1 := Nat.factorial_mul_descFactorial (le_trans hmk hk)
  have e2 := Nat.factorial_mul_descFactorial hk
  have key : (a - m)! * Nat.descFactorial a m = (a - k)! * Nat.descFactorial a k := by
    rw [e1, e2]
  have hfle : (a - k)! ≤ (a - m)! := Nat.factorial_le (by omega)
  have hstep : (a - m)! * Nat.descFactorial a m ≤ (a - m)! * Nat.descFactorial a k := by
    rw [key]; exact Nat.mul_le_mul hfle (le_refl _)
  exact Nat.le_of_mul_le_mul_left hstep (Nat.factorial_pos _)

/-- the descending-factorial bound for one term. -/
lemma desc_sub1 (n k j : ℕ) (hk : k + 1 ≤ n) (hj4 : j ≤ 4) (hjk : j ≤ k) :
    Nat.descFactorial (2 * n + j - (k + 10)) (k - j)
      ≤ 2 ^ (k - j) * Nat.descFactorial (n - 1) (k - j) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
    show (2 : ℕ) ^ (k - j) = ∏ _i ∈ Finset.range (k - j), 2 by
      rw [Finset.prod_const, Finset.card_range],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro i hi
  have hilt : i < k - j := Finset.mem_range.mp hi
  omega

/-- bound for a single term of `F`. -/
lemma term_bound (n k j : ℕ) (hk : k + 1 ≤ n) (hj4 : j ≤ 4) (hjk : j ≤ k) :
    (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) / (Nat.descFactorial (n - 1) k : ℝ)
      ≤ (2 : ℝ) ^ (k - j) / ((k - j)! : ℝ) := by
  have hkn : k ≤ n - 1 := by omega
  have hdpos : 0 < Nat.descFactorial (n - 1) k := Nat.descFactorial_pos.mpr hkn
  have hnat : Nat.descFactorial (2 * n + j - (k + 10)) (k - j)
      ≤ 2 ^ (k - j) * Nat.descFactorial (n - 1) k := by
    calc Nat.descFactorial (2 * n + j - (k + 10)) (k - j)
        ≤ 2 ^ (k - j) * Nat.descFactorial (n - 1) (k - j) := desc_sub1 n k j hk hj4 hjk
      _ ≤ 2 ^ (k - j) * Nat.descFactorial (n - 1) k :=
          Nat.mul_le_mul (le_refl _) (descFactorial_mono_right (n - 1) (k - j) k (by omega) hkn)
  rw [div_le_div_iff₀ (by exact_mod_cast hdpos) (by positivity)]
  have hcm : (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) * ((k - j)! : ℝ)
      = (Nat.descFactorial (2 * n + j - (k + 10)) (k - j) : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  rw [hcm]
  calc (Nat.descFactorial (2 * n + j - (k + 10)) (k - j) : ℝ)
      ≤ ((2 ^ (k - j) * Nat.descFactorial (n - 1) k : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ (k - j) * (Nat.descFactorial (n - 1) k : ℝ) := by push_cast; ring

/-- summability is closed under finite sums of summable families. -/
lemma summable_finset_sum_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ → ℝ)
    (h : ∀ i ∈ s, Summable (f i)) : Summable (fun k => ∑ i ∈ s, f i k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using summable_zero
  | @insert a s ha ih =>
    have h1 : Summable (f a) := h a (Finset.mem_insert_self _ _)
    have h2 : Summable (fun k => ∑ i ∈ s, f i k) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have : (fun k => ∑ i ∈ insert a s, f i k) = (fun k => f a k + ∑ i ∈ s, f i k) := by
      funext k; rw [Finset.sum_insert ha]
    rw [this]
    exact h1.add h2

/-- the dominating sequence. -/
noncomputable def boundSeq (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 5, (Nat.choose (8 - j) j : ℝ) *
    (if j ≤ k then (2 : ℝ) ^ (k - j) / ((k - j)! : ℝ) else 0)

lemma boundSeq_nonneg (k : ℕ) : 0 ≤ boundSeq k := by
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (by positivity)
  split <;> positivity

lemma summable_boundSeq : Summable boundSeq := by
  apply summable_finset_sum_aux
  intro j _
  apply Summable.mul_left
  -- Summable (fun k => if j ≤ k then 2^(k-j)/(k-j)! else 0)
  set g : ℕ → ℝ := fun k => if j ≤ k then (2 : ℝ) ^ (k - j) / ((k - j)! : ℝ) else 0 with hg
  have hinj : Function.Injective (fun m : ℕ => m + j) := add_left_injective j
  have hzero : ∀ x : ℕ, x ∉ Set.range (fun m : ℕ => m + j) → g x = 0 := by
    intro x hx
    have : x < j := by
      by_contra h
      push_neg at h
      exact hx ⟨x - j, by show x - j + j = x; omega⟩
    simp only [hg]
    rw [if_neg (by omega)]
  rw [← Function.Injective.summable_iff hinj hzero]
  have hcomp : (g ∘ (fun m : ℕ => m + j)) = (fun m => (2 : ℝ) ^ m / (m ! : ℝ)) := by
    funext m
    simp only [hg, Function.comp_apply]
    have hsub : m + j - j = m := by omega
    rw [if_pos (by omega), hsub]
  rw [hcomp]
  exact Real.summable_pow_div_factorial 2

lemma inner_nonneg (n k : ℕ) : 0 ≤ A258667_inner_sum n k := by
  rw [A258667_inner_sum]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

lemma inner_real (n k : ℕ) : (A258667_inner_sum n k : ℝ)
    = ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
        (Nat.choose (8 - j) j : ℝ) * (Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ) := by
  rw [A258667_inner_sum]
  push_cast [Int.ofNat_eq_natCast]
  rfl

/-- the dominating bound for `F`. -/
lemma F_bound (n k : ℕ) : ‖F n k‖ ≤ boundSeq k := by
  rcases Nat.lt_or_ge k n with hkn | hnk
  · -- k < n
    have hk1 : k + 1 ≤ n := hkn
    have hdpos : 0 < (Nat.descFactorial (n - 1) k : ℝ) := by
      have := Nat.descFactorial_pos.mpr (show k ≤ n - 1 by omega)
      exact_mod_cast this
    have hnorm : ‖F n k‖
        = (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ) := by
      rw [F, norm_div, norm_mul]
      rw [show ‖((-1 : ℝ) ^ k)‖ = 1 by rw [norm_pow, norm_neg, norm_one, one_pow]]
      rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast inner_nonneg n k)]
      rw [Real.norm_eq_abs (Nat.descFactorial (n - 1) k : ℝ), abs_of_nonneg (le_of_lt hdpos)]
      rw [one_mul]
    rw [hnorm]
    -- p j is the boundSeq summand
    set p : ℕ → ℝ := fun j => (Nat.choose (8 - j) j : ℝ) *
      (if j ≤ k then (2 : ℝ) ^ (k - j) / ((k - j)! : ℝ) else 0) with hp
    have hpnn : ∀ j, 0 ≤ p j := by
      intro j; simp only [hp]; apply mul_nonneg (by positivity); split <;> positivity
    have hsubset : Finset.Icc (max 0 (k + 5 - n)) (min k 4) ⊆ Finset.range 5 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      have : j ≤ min k 4 := hj.2
      omega
    calc (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ)
        = ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
            (Nat.choose (8 - j) j : ℝ) *
              ((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℝ)
                / (Nat.descFactorial (n - 1) k : ℝ)) := by
          rw [inner_real, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _; rw [mul_div_assoc]
      _ ≤ ∑ j ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4), p j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_Icc] at hj
          have hjU : j ≤ min k 4 := hj.2
          have hj4 : j ≤ 4 := le_trans hjU (min_le_right _ _)
          have hjk : j ≤ k := le_trans hjU (min_le_left _ _)
          simp only [hp, if_pos hjk]
          apply mul_le_mul_of_nonneg_left (term_bound n k j hk1 hj4 hjk) (by positivity)
      _ ≤ ∑ j ∈ Finset.range 5, p j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j _ _ => hpnn j)
      _ = boundSeq k := rfl
  · -- k ≥ n : F = 0
    by_cases hn1 : 1 ≤ n
    · have hd0 : Nat.descFactorial (n - 1) k = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      have hF0 : F n k = 0 := by rw [F, hd0]; simp
      rw [hF0, norm_zero]; exact boundSeq_nonneg k
    · have hn0 : n = 0 := by omega
      have hinner : (A258667_inner_sum n k : ℝ) = 0 := by
        rw [inner_real]
        rw [Finset.Icc_eq_empty (by subst hn0; omega), Finset.sum_empty]
      have hF0 : F n k = 0 := by rw [F, hinner]; simp
      rw [hF0, norm_zero]; exact boundSeq_nonneg k

/-- the running partial-limit `T n = ∑\' k, F n k`. -/
noncomputable def T (n : ℕ) : ℝ := ∑' k, F n k

lemma hasSum_exp_neg_two :
    HasSum (fun k : ℕ => (-2 : ℝ) ^ k / (k ! : ℝ)) (Real.exp (-2)) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp (-2 : ℝ)

lemma tsum_g : ∑' k : ℕ, (-2 : ℝ) ^ k / (k ! : ℝ) = Real.exp (-2) :=
  hasSum_exp_neg_two.tsum_eq

/-- Tannery's theorem gives the limit of `T`. -/
lemma T_tendsto : Tendsto T atTop (𝓝 (Real.exp (-2))) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun n k => F n k)
    (g := fun k => (-2 : ℝ) ^ k / (k ! : ℝ)) (bound := boundSeq)
    summable_boundSeq F_limit (Eventually.of_forall (fun n k => F_bound n k))
  rw [tsum_g] at h
  exact h

/-- `T n` is a finite sum over `range n`. -/
lemma T_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    T n = ∑ k ∈ Finset.range n, F n k := by
  rw [T, tsum_eq_sum (s := Finset.range n)]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have hd0 : Nat.descFactorial (n - 1) k = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
  rw [F, hd0]; simp

/-- the key identity relating `A258667` and `T`. -/
lemma A_eq_factorial_mul_abs_T (n : ℕ) (hn : 5 < n) :
    (A258667 n : ℝ) = (Nat.factorial (n - 1) : ℝ) * |T n| := by
  have hn1 : 1 ≤ n := by omega
  -- the integer sum
  set Sint : ℤ := Finset.sum (Finset.range n) fun k =>
    (if k % 2 = 0 then (1 : ℤ) else -1) * (ofNat (Nat.factorial (n - 1 - k))) *
      A258667_inner_sum n k with hSint
  have hA : A258667 n = Sint.natAbs := by
    rw [A258667, dif_neg (by omega)]
  -- (n-1)! * T n = Sint  (as reals)
  have hkey : (Nat.factorial (n - 1) : ℝ) * T n = (Sint : ℝ) := by
    rw [T_eq_sum n hn1, Finset.mul_sum, hSint]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    -- (n-1)! * F n k = sign * (n-1-k)! * inner
    have hkn1 : k ≤ n - 1 := by omega
    have hdpos : 0 < Nat.descFactorial (n - 1) k := Nat.descFactorial_pos.mpr hkn1
    have hfac : ((Nat.factorial (n - 1) : ℝ))
        = (Nat.factorial (n - 1 - k) : ℝ) * (Nat.descFactorial (n - 1) k : ℝ) := by
      have := Nat.factorial_mul_descFactorial (show k ≤ n - 1 from hkn1)
      have hcast : ((Nat.factorial (n - 1 - k) * Nat.descFactorial (n - 1) k : ℕ) : ℝ)
          = (Nat.factorial (n - 1) : ℝ) := by exact_mod_cast this
      push_cast at hcast
      linarith [hcast]
    rw [F]
    have hsign : (if k % 2 = 0 then (1 : ℝ) else -1) = (-1 : ℝ) ^ k := by
      rcases Nat.even_or_odd k with he | ho
      · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow]
      · rw [if_neg (by simp [Nat.odd_iff.mp ho]), ho.neg_one_pow]
    rw [hfac]
    field_simp
    rw [hsign]
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [hA]
  rw [show ((Sint.natAbs : ℕ) : ℝ) = |(Sint : ℝ)| from by
    rw [Int.cast_natAbs]; push_cast; rfl]
  rw [← hkey, abs_mul, abs_of_nonneg (by positivity)]

/-- the summand of the asymptotic sum part. -/
noncomputable def Gterm (n k : ℕ) : ℝ :=
  if k = 0 then 0
  else if menage_denom_term n k = 0 then 0 else ((-1 : ℝ) ^ k) / menage_denom_term n k

lemma sumpart_eq (n : ℕ) :
    A258667_asymptotic_sum_part n = ∑ k ∈ Finset.range n, Gterm n k := rfl

lemma menage_denom_eq (n k : ℕ) :
    menage_denom_term n k = (k ! : ℝ) * (Nat.descFactorial (n - 1) k : ℝ) := rfl

lemma Gterm_bound (n k : ℕ) : ‖Gterm n k‖ ≤ (1 : ℝ) ^ k / (k ! : ℝ) := by
  rw [one_pow]
  rw [Gterm]
  split
  · rw [norm_zero]; positivity
  · split
    · rw [norm_zero]; positivity
    · rename_i hk0 hdne
      have hdpos : 0 < menage_denom_term n k :=
        lt_of_le_of_ne (by rw [menage_denom_eq]; positivity) (Ne.symm hdne)
      have hdescge : 1 ≤ Nat.descFactorial (n - 1) k := by
        rcases Nat.eq_zero_or_pos (Nat.descFactorial (n - 1) k) with h | h
        · exfalso; apply hdne; rw [menage_denom_eq, h]; simp
        · exact h
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
        abs_of_pos hdpos, menage_denom_eq]
      have hkfac : (k ! : ℝ) ≤ (k ! : ℝ) * (Nat.descFactorial (n - 1) k : ℝ) :=
        le_mul_of_one_le_right (by positivity) (by exact_mod_cast hdescge)
      exact one_div_le_one_div_of_le (by positivity) hkfac

/-- per-`k` limit of `Gterm`. -/
lemma Gterm_limit (k : ℕ) : Tendsto (fun n => Gterm n k) atTop (𝓝 0) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Gterm]
    exact tendsto_const_nhds
  · have hkne : k ≠ 0 := hk0
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ k) atTop atTop :=
      (tendsto_pow_atTop hkne).comp tendsto_natCast_atTop_atTop
    have hbig : Tendsto (fun n => (Nat.descFactorial (n - 1) k : ℝ)) atTop atTop := by
      have hmul := Filter.Tendsto.pos_mul_atTop (C := 1) one_pos
        (descFactorial_div_limit k) hpow
      refine hmul.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn0
      have : (n : ℝ) ^ k ≠ 0 := by positivity
      field_simp
    have hdenom : Tendsto (fun n => menage_denom_term n k) atTop atTop := by
      have := Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < (k ! : ℝ) by positivity) hbig
      refine this.congr' ?_
      filter_upwards with n
      rw [menage_denom_eq]
    have hinv : Tendsto (fun n => (menage_denom_term n k)⁻¹) atTop (𝓝 0) :=
      hdenom.inv_tendsto_atTop
    have hg := hinv.const_mul ((-1 : ℝ) ^ k)
    rw [mul_zero] at hg
    refine hg.congr' ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    have hdne : menage_denom_term n k ≠ 0 := by
      rw [menage_denom_eq]
      have : 0 < Nat.descFactorial (n - 1) k := Nat.descFactorial_pos.mpr (by omega)
      positivity
    rw [Gterm, if_neg hk0, if_neg hdne, div_eq_mul_inv]

/-- the asymptotic sum part tends to 0. -/
lemma sp_tendsto : Tendsto A258667_asymptotic_sum_part atTop (𝓝 0) := by
  have hsummable : Summable (fun k => (1 : ℝ) ^ k / (k ! : ℝ)) :=
    Real.summable_pow_div_factorial 1
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun n k => Gterm n k) (g := fun _ => (0 : ℝ))
    (bound := fun k => (1 : ℝ) ^ k / (k ! : ℝ))
    hsummable Gterm_limit (Eventually.of_forall (fun n k => Gterm_bound n k))
  rw [tsum_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  rw [sumpart_eq, tsum_eq_sum (s := Finset.range n)]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  by_cases hk0 : k = 0
  · rw [Gterm, if_pos hk0]
  · rw [Gterm, if_neg hk0, if_pos]
    rw [menage_denom_eq, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- the comparison function `e^{-2} (n-1)!`. -/
noncomputable def hcomp (n : ℕ) : ℝ := Real.exp (-2) * (Nat.factorial (n - 1) : ℝ)

lemma equiv_A : (fun n : ℕ => (A258667 n : ℝ)) ~[atTop] hcomp := by
  have hz : ∀ᶠ n in atTop, hcomp n ≠ 0 :=
    Eventually.of_forall (fun n => (show (0:ℝ) < hcomp n by rw [hcomp]; positivity).ne')
  rw [isEquivalent_iff_tendsto_one hz]
  · have habsT : Tendsto (fun n => |T n|) atTop (𝓝 (Real.exp (-2))) := by
      have h := (continuous_abs.tendsto _).comp T_tendsto
      rwa [abs_of_pos (Real.exp_pos _)] at h
    have hratio : Tendsto (fun n => |T n| / Real.exp (-2)) atTop (𝓝 1) := by
      have h := habsT.div_const (Real.exp (-2))
      rwa [div_self (ne_of_gt (Real.exp_pos _))] at h
    refine hratio.congr' ?_
    filter_upwards [eventually_gt_atTop 5] with n hn
    simp only [Pi.div_apply]
    rw [A_eq_factorial_mul_abs_T n hn, hcomp]
    have hf : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by positivity
    have he : Real.exp (-2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp

lemma equiv_asym : A258667_asymptotic_term ~[atTop] hcomp := by
  have hz : ∀ᶠ n in atTop, hcomp n ≠ 0 :=
    Eventually.of_forall (fun n => (show (0:ℝ) < hcomp n by rw [hcomp]; positivity).ne')
  rw [isEquivalent_iff_tendsto_one hz]
  · have hd : Tendsto (fun n : ℕ => ((n : ℝ) - 2) / (n : ℝ)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 2 / (n : ℝ)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn0
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 2)) atTop (𝓝 1) := by
      have := hd.inv₀ (one_ne_zero)
      rw [inv_one] at this
      refine this.congr (fun n => ?_)
      rw [inv_div]
    have h2 : Tendsto (fun n => 1 + A258667_asymptotic_sum_part n) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add sp_tendsto
      simpa using this
    have hmul := h1.mul h2
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 2] with n hn
    simp only [Pi.div_apply]
    have hn1 : 1 ≤ n := by omega
    have hfact : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
      have h := Nat.factorial_succ (n - 1)
      rw [Nat.sub_add_cancel hn1] at h
      exact_mod_cast h
    have he : Real.exp (-2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hf : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by positivity
    have hn2 : (n : ℝ) - 2 ≠ 0 := by
      have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [A258667_asymptotic_term, if_neg (by omega : ¬ n ≤ 2)]
    simp only [nat_fac_to_real]
    rw [hcomp, hfact]
    field_simp


/--
A258667 Conjecture:
Therefore, it is natural to conjecture that a(n) ~ e^(-2)*n!/(n-2)*(1 + Sum_{k>=1} (-1)^k/(k!(n-1)_k)).
-/
theorem oeis_A258667_conjecture_0 :
  IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) A258667_asymptotic_term :=
  equiv_A.trans equiv_asym.symm
