import FormalConjectures.Util.ProblemImports

open BigOperators Nat Int Real Asymptotics Filter Topology

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


/-! Auxiliary lemmas for the asymptotic evaluation of the inclusion--exclusion sum. -/

lemma top_equiv (k j : ℕ) :
    (fun n : ℕ => ((2 * n + j - (k + 10) : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => (2 : ℝ) * n) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn hzero
    have : (2:ℝ) * n ≠ 0 := by positivity
    exfalso
    exact this hzero
  · have ht : Tendsto (fun n : ℕ => ((j : ℝ) - (k + 10 : ℝ) + (2 : ℝ) * n) / (0 + (2 : ℝ) * n)) atTop (𝓝 (((2:ℝ)/(2:ℝ)))) :=
      tendsto_add_mul_div_add_mul_atTop_nhds ((j : ℝ) - (k + 10 : ℝ)) (0:ℝ) (2:ℝ) (by norm_num : (2:ℝ) ≠ 0)
    have htc : Tendsto (fun n : ℕ => ((j : ℝ) - (k + 10 : ℝ) + (2 : ℝ) * n) / (0 + (2 : ℝ) * n)) atTop (𝓝 (1:ℝ)) := by
      simpa using ht
    refine htc.congr' ?_
    filter_upwards [eventually_ge_atTop (k + 10)] with n hn
    dsimp
    have hsub : k + 10 ≤ 2 * n + j := by nlinarith [hn]
    rw [Nat.cast_sub hsub]
    norm_num
    ring

lemma sub_one_equiv :
    (fun n : ℕ => ((n - 1 : ℕ) : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn hzero
    have : (n : ℝ) ≠ 0 := by positivity
    exfalso; exact this hzero
  · have ht : Tendsto (fun n : ℕ => ((-1 : ℝ) + (1 : ℝ) * n) / (0 + (1 : ℝ) * n)) atTop (𝓝 (((1:ℝ)/(1:ℝ)))) :=
      tendsto_add_mul_div_add_mul_atTop_nhds (-1:ℝ) (0:ℝ) (1:ℝ) (by norm_num : (1:ℝ) ≠ 0)
    have htc : Tendsto (fun n : ℕ => ((-1 : ℝ) + (1 : ℝ) * n) / (0 + (1 : ℝ) * n)) atTop (𝓝 (1:ℝ)) := by simpa using ht
    refine htc.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp
    rw [Nat.cast_sub hn]
    norm_num
    ring

lemma desc_shift_equiv (k : ℕ) :
    (fun n : ℕ => (((n - 1).descFactorial k : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ k) := by
  have hcomp := (isEquivalent_descFactorial k).comp_tendsto (show Tendsto (fun n : ℕ => n - 1) atTop atTop by
    exact tendsto_atTop_atTop.mpr (fun b => ⟨b+1, by intro a ha; omega⟩))
  -- hcomp target is ((n-1:ℕ):ℝ)^k
  exact hcomp.trans (sub_one_equiv.pow k)

lemma top_tendsto_atTop (k j : ℕ) : Tendsto (fun n : ℕ => 2 * n + j - (k + 10)) atTop atTop := by
  exact tendsto_atTop_atTop.mpr (fun b => ⟨b + k + 10, by intro a ha; omega⟩)

lemma choose_shift_equiv (r k j : ℕ) :
    (fun n : ℕ => ((Nat.choose (2 * n + j - (k + 10)) r : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => ((2 : ℝ) * n) ^ r / (Nat.factorial r : ℝ)) := by
  have h1 := (isEquivalent_choose r).comp_tendsto (top_tendsto_atTop k j)
  have htop_pow := (top_equiv k j).pow r
  have h2 : (fun n : ℕ => (((2 * n + j - (k + 10) : ℕ) : ℝ) ^ r / (Nat.factorial r : ℝ))) ~[atTop]
      (fun n : ℕ => (((2 : ℝ) * n) ^ r / (Nat.factorial r : ℝ))) := by
    exact htop_pow.div IsEquivalent.refl
  exact h1.trans h2

lemma choose_div_desc_tendsto (k j : ℕ) (hj : j ≤ k) :
    Tendsto (fun n : ℕ => ((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℕ) : ℝ) /
        (((n - 1).descFactorial k : ℕ) : ℝ)) atTop
      (𝓝 (if j = 0 then (2 : ℝ) ^ k / (Nat.factorial k : ℝ) else 0)) := by
  let r := k - j
  have hnum := choose_shift_equiv r k j
  have hden := desc_shift_equiv k
  have hratio := hnum.div hden
  have htarget : Tendsto (fun n : ℕ => (((2 : ℝ) * n) ^ r / (Nat.factorial r : ℝ)) / ((n : ℝ) ^ k)) atTop
      (𝓝 (if j = 0 then (2 : ℝ) ^ k / (Nat.factorial k : ℝ) else 0)) := by
    by_cases h0 : j = 0
    · subst j
      simp only [tsub_zero, r]
      have hc : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k ≠ 0 := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        positivity
      have heq : (fun n : ℕ => (((2 : ℝ) * n) ^ k / (Nat.factorial k : ℝ)) / ((n : ℝ) ^ k)) =ᶠ[atTop]
          (fun _ : ℕ => (2 : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        field_simp [hn0]
        ring
      exact tendsto_const_nhds.congr' heq.symm
    · have hrlt : r < k := by
        dsimp [r]
        omega
      have hpow : Tendsto (fun n : ℕ => ((n : ℝ) ^ r / (n : ℝ) ^ k)) atTop (𝓝 (0:ℝ)) := by
        simpa using ((tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) hrlt).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
      have hc : Tendsto (fun n : ℕ => (2:ℝ)^r / (Nat.factorial r : ℝ) * (((n:ℝ)^r) / ((n:ℝ)^k))) atTop (𝓝 ((2:ℝ)^r / (Nat.factorial r : ℝ) * 0)) :=
        tendsto_const_nhds.mul hpow
      have heq : (fun n : ℕ => (((2 : ℝ) * n) ^ r / (Nat.factorial r : ℝ)) / ((n : ℝ) ^ k)) =
          (fun n : ℕ => (2:ℝ)^r / (Nat.factorial r : ℝ) * (((n:ℝ)^r) / ((n:ℝ)^k))) := by
        funext n
        ring
      simpa [h0, heq]
        using hc
  exact hratio.tendsto_nhds_iff.mpr htarget

noncomputable def A258667_norm_summand (n k : ℕ) : ℝ :=
  if n ≤ 5 then 0 else
  if k < n then
    ((-1 : ℝ)^k) * ((Nat.factorial (n - 1 - k) : ℝ) / (Nat.factorial (n - 1) : ℝ)) *
      (A258667_inner_sum n k : ℝ)
  else 0

lemma factorial_ratio_eq_inv_desc {n k : ℕ} (hk : k ≤ n - 1) :
    ((Nat.factorial (n - 1 - k) : ℝ) / (Nat.factorial (n - 1) : ℝ)) =
      1 / (((n - 1).descFactorial k : ℕ) : ℝ) := by
  have hmul := Nat.factorial_mul_descFactorial (n := n - 1) (k := k) hk
  have hcast : ((Nat.factorial (n - 1 - k) : ℝ) * (((n - 1).descFactorial k : ℕ) : ℝ)) = (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast hmul
  have hfac : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by positivity
  have hdesc : (((n - 1).descFactorial k : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (n - 1).descFactorial k := Nat.descFactorial_pos.mpr hk
    positivity
  field_simp [hfac, hdesc]
  exact hcast

lemma norm_summand_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => A258667_norm_summand n k) atTop
      (𝓝 (((-2 : ℝ)^k) / (Nat.factorial k : ℝ))) := by
  have hfinite : Tendsto (fun n : ℕ =>
      ((-1 : ℝ)^k) * (∑ j ∈ Finset.Icc 0 (min k 4),
        ((Nat.choose (8 - j) j : ℕ) : ℝ) *
          (((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℕ) : ℝ) /
            (((n - 1).descFactorial k : ℕ) : ℝ)))) atTop
      (𝓝 (((-2 : ℝ)^k) / (Nat.factorial k : ℝ))) := by
    have hsum : Tendsto (fun n : ℕ => (∑ j ∈ Finset.Icc 0 (min k 4),
        ((Nat.choose (8 - j) j : ℕ) : ℝ) *
          (((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℕ) : ℝ) /
            (((n - 1).descFactorial k : ℕ) : ℝ)))) atTop
      (𝓝 ((2 : ℝ)^k / (Nat.factorial k : ℝ))) := by
      have htend : Tendsto (fun n : ℕ => (∑ j ∈ Finset.Icc 0 (min k 4),
          ((Nat.choose (8 - j) j : ℕ) : ℝ) *
            (((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℕ) : ℝ) /
              (((n - 1).descFactorial k : ℕ) : ℝ)))) atTop
        (𝓝 (∑ j ∈ Finset.Icc 0 (min k 4),
          (if j = 0 then (2 : ℝ)^k / (Nat.factorial k : ℝ) else 0))) := by
        apply tendsto_finset_sum
        intro j hj
        have hjk : j ≤ k := by exact le_trans (Finset.mem_Icc.mp hj).2 (min_le_left k 4)
        have ht := choose_div_desc_tendsto k j hjk
        have hmul := (tendsto_const_nhds.mul ht :
          Tendsto (fun b : ℕ => ((Nat.choose (8 - j) j : ℕ) : ℝ) *
            (((Nat.choose (2 * b + j - (k + 10)) (k - j) : ℕ) : ℝ) /
              (((b - 1).descFactorial k : ℕ) : ℝ))) atTop
            (𝓝 (((Nat.choose (8 - j) j : ℕ) : ℝ) *
              (if j = 0 then (2 : ℝ)^k / (Nat.factorial k : ℝ) else 0))))
        convert hmul using 1
        by_cases h0 : j = 0 <;> simp [h0]
      convert htend using 1
      simp
    have hmul : Tendsto (fun n : ℕ => ((-1 : ℝ)^k) * (∑ j ∈ Finset.Icc 0 (min k 4),
        ((Nat.choose (8 - j) j : ℕ) : ℝ) *
          (((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℕ) : ℝ) /
            (((n - 1).descFactorial k : ℕ) : ℝ)))) atTop
        (𝓝 (((-1 : ℝ)^k) * ((2 : ℝ)^k / (Nat.factorial k : ℝ)))) := by
      exact tendsto_const_nhds.mul hsum
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ← mul_pow] using hmul
  refine hfinite.congr' ?_
  filter_upwards [eventually_ge_atTop (max 6 (k + 5))] with n hn
  dsimp [A258667_norm_summand, A258667_inner_sum]
  have hn5 : ¬ n ≤ 5 := by omega
  have hkn : k < n := by omega
  simp [hn5, hkn]
  have hk_le : k ≤ n - 1 := by omega
  rw [factorial_ratio_eq_inv_desc hk_le]
  have hsub0 : k + 5 - n = 0 := by omega
  simp [hsub0]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hden : (((n - 1).descFactorial k : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (n - 1).descFactorial k := Nat.descFactorial_pos.mpr hk_le
    positivity
  field_simp [hden]

lemma top_desc_le (n k j : ℕ) (hj : j ≤ k) :
    (2 * n + j - (k + 10)).descFactorial (k - j) ≤
      2 ^ (k - j) * (n - 1).descFactorial (k - j) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  have hprod : (∏ i ∈ Finset.range (k - j), (2 * n + j - (k + 10) - i)) ≤
      ∏ i ∈ Finset.range (k - j), (2 * (n - 1 - i)) := by
    apply Finset.prod_le_prod'
    intro i hi
    rw [Finset.mem_range] at hi
    omega
  calc
    (∏ i ∈ Finset.range (k - j), (2 * n + j - (k + 10) - i)) ≤
        ∏ i ∈ Finset.range (k - j), (2 * (n - 1 - i)) := hprod
    _ = 2 ^ (k - j) * ∏ i ∈ Finset.range (k - j), (n - 1 - i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

lemma desc_len_le (N r k : ℕ) (hr : r ≤ k) (hk : k ≤ N) :
    N.descFactorial r ≤ N.descFactorial k := by
  rcases Nat.exists_eq_add_of_le hr with ⟨d, rfl⟩
  have heq := (Nat.descFactorial_mul_descFactorial (n := N) (k := r) (m := r + d) (by omega)).symm
  rw [heq]
  exact Nat.le_mul_of_pos_left (N.descFactorial r) (Nat.descFactorial_pos.mpr (by omega : r + d - r ≤ N - r))

lemma choose_div_desc_le_bound (n k j : ℕ) (hjk : j ≤ k) (hkn : k < n) :
    ((Nat.choose (2 * n + j - (k + 10)) (k - j) : ℕ) : ℝ) /
        (((n - 1).descFactorial k : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (k - j) / (Nat.factorial (k - j) : ℝ) := by
  let r := k - j
  have hkN : k ≤ n - 1 := by omega
  have hdescpos : 0 < (n - 1).descFactorial k := Nat.descFactorial_pos.mpr hkN
  have hfacpos : 0 < Nat.factorial r := Nat.factorial_pos r
  have hchoose_desc : Nat.choose (2 * n + j - (k + 10)) r * Nat.factorial r ≤
      2 ^ r * (n - 1).descFactorial k := by
    have h_eq := Nat.descFactorial_eq_factorial_mul_choose (2 * n + j - (k + 10)) r
    have htop := top_desc_le n k j hjk
    have hlen : (n - 1).descFactorial r ≤ (n - 1).descFactorial k := by
      exact desc_len_le (n - 1) r k (by dsimp [r]; omega) hkN
    calc
      Nat.choose (2 * n + j - (k + 10)) r * Nat.factorial r =
          (2 * n + j - (k + 10)).descFactorial r := by
            rw [mul_comm, h_eq]
      _ ≤ 2 ^ r * (n - 1).descFactorial r := top_desc_le n k j hjk
      _ ≤ 2 ^ r * (n - 1).descFactorial k := Nat.mul_le_mul_left _ hlen
  have hreal : (((Nat.choose (2 * n + j - (k + 10)) r * Nat.factorial r : ℕ) : ℝ) ≤
      ((2 ^ r * (n - 1).descFactorial k : ℕ) : ℝ)) := by exact_mod_cast hchoose_desc
  dsimp [r] at hreal ⊢
  have hdenpos : 0 < (((n - 1).descFactorial k : ℕ) : ℝ) := by positivity
  have hfacposR : 0 < ((Nat.factorial (k - j) : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hdenpos hfacposR]
  simpa [Nat.cast_mul] using hreal

noncomputable def A258667_bound (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 5, ((Nat.choose (8 - j) j : ℕ) : ℝ) *
    (if j ≤ k then (2 : ℝ) ^ (k - j) / (Nat.factorial (k - j) : ℝ) else 0)

lemma summable_shift_exp (j : ℕ) :
    Summable (fun k : ℕ => if j ≤ k then (2 : ℝ) ^ (k - j) / (Nat.factorial (k - j) : ℝ) else 0) := by
  let f : ℕ → ℝ := fun k => if j ≤ k then (2 : ℝ) ^ (k - j) / (Nat.factorial (k - j) : ℝ) else 0
  have hbase : Summable (fun n : ℕ => (2 : ℝ)^n / (Nat.factorial n : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (2 : ℝ)).summable
  have hshift : Summable (fun n : ℕ => f (n + j)) := by
    simpa [f, Nat.add_sub_cancel_left] using hbase
  exact Summable.comp_nat_add hshift

lemma summable_A258667_bound : Summable A258667_bound := by
  let term : ℕ → ℕ → ℝ := fun j k => ((Nat.choose (8 - j) j : ℕ) : ℝ) *
    (if j ≤ k then (2 : ℝ) ^ (k - j) / (Nat.factorial (k - j) : ℝ) else 0)
  have hfin : ∀ s : Finset ℕ, Summable (fun k : ℕ => ∑ j ∈ s, term j k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    | insert a s has ih =>
        have ha : Summable (fun k : ℕ => term a k) := by
          dsimp [term]
          exact Summable.mul_left _ (summable_shift_exp a)
        simpa [Finset.sum_insert has, term] using ha.add ih
  change Summable (fun k : ℕ => ∑ j ∈ Finset.range 5, term j k)
  exact hfin (Finset.range 5)

lemma norm_summand_le_bound :
    ∀ᶠ n in atTop, ∀ k, ‖A258667_norm_summand n k‖ ≤ A258667_bound k := by
  filter_upwards [eventually_ge_atTop 6] with n hn k
  by_cases hkn : k < n
  · have hn5 : ¬ n ≤ 5 := by omega
    have hkN : k ≤ n - 1 := by omega
    dsimp [A258667_norm_summand, A258667_inner_sum]
    simp [hn5, hkn]
    rw [factorial_ratio_eq_inv_desc hkN]
    -- simplify norm of sign and reciprocal times nonnegative sum using crude abs_sum bound
    have hdenpos : 0 < (((n - 1).descFactorial k : ℕ) : ℝ) := by
      have hpos : 0 < (n - 1).descFactorial k := Nat.descFactorial_pos.mpr hkN
      positivity
    calc
      _ = |(∑ x ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
              ((Nat.choose (8 - x) x : ℕ) : ℝ) *
              (((Nat.choose (2 * n + x - (k + 10)) (k - x) : ℕ) : ℝ) /
                (((n - 1).descFactorial k : ℕ) : ℝ)))| := by
            simp only [max_eq_right (Nat.zero_le (k + 5 - n))]
            rw [abs_of_pos (show 0 < (1 / (((n - 1).descFactorial k : ℕ) : ℝ)) by positivity)]
            rw [abs_of_nonneg]
            swap
            · apply Finset.sum_nonneg
              intro j hj; positivity
            rw [abs_of_nonneg]
            swap
            · apply Finset.sum_nonneg
              intro j hj
              apply mul_nonneg <;> positivity
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            field_simp [ne_of_gt hdenpos]
      _ ≤ ∑ x ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
              |((Nat.choose (8 - x) x : ℕ) : ℝ) *
              (((Nat.choose (2 * n + x - (k + 10)) (k - x) : ℕ) : ℝ) /
                (((n - 1).descFactorial k : ℕ) : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Finset.Icc (max 0 (k + 5 - n)) (min k 4),
              ((Nat.choose (8 - x) x : ℕ) : ℝ) *
              ((2 : ℝ) ^ (k - x) / (Nat.factorial (k - x) : ℝ)) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjk : j ≤ k := by exact le_trans (Finset.mem_Icc.mp hj).2 (min_le_left k 4)
            have hnonnegC : 0 ≤ ((Nat.choose (8 - j) j : ℕ) : ℝ) := by positivity
            rw [abs_of_nonneg]
            · exact mul_le_mul_of_nonneg_left (choose_div_desc_le_bound n k j hjk hkn) hnonnegC
            · exact mul_nonneg hnonnegC (div_nonneg (by positivity) (by positivity))
      _ ≤ A258667_bound k := by
            dsimp [A258667_bound]
            let s := Finset.Icc (max 0 (k + 5 - n)) (min k 4)
            let g : ℕ → ℝ := fun j => ((Nat.choose (8 - j) j : ℕ) : ℝ) *
              (if j ≤ k then (2 : ℝ) ^ (k - j) / (Nat.factorial (k - j) : ℝ) else 0)
            have h₁ : (∑ x ∈ s, ((Nat.choose (8 - x) x : ℕ) : ℝ) *
                ((2 : ℝ) ^ (k - x) / (Nat.factorial (k - x) : ℝ))) ≤ ∑ x ∈ s, g x := by
              apply Finset.sum_le_sum
              intro j hj
              have hjk : j ≤ k := by exact le_trans (Finset.mem_Icc.mp hj).2 (min_le_left k 4)
              simp [g, hjk]
            have h₂ : (∑ x ∈ s, g x) ≤ ∑ j ∈ Finset.range 5, g j := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro j hj
                rw [Finset.mem_range]
                have hj4 : j ≤ 4 := le_trans (Finset.mem_Icc.mp hj).2 (min_le_right k 4)
                omega
              · intro j hjrange hnot
                dsimp [g]
                split <;> positivity
            exact le_trans h₁ h₂
  · dsimp [A258667_norm_summand]
    by_cases hn5 : n ≤ 5
    · simp [hn5]
      dsimp [A258667_bound]
      positivity
    · simp [hn5, hkn]
      dsimp [A258667_bound]
      positivity


noncomputable def A258667_signed_sum (n : ℕ) : ℤ :=
  if n ≤ 5 then 0 else
  Finset.sum (Finset.range n) fun k =>
    let sign : ℤ := if k % 2 = 0 then 1 else -1
    let fac_term : ℤ := ofNat (Nat.factorial (n - 1 - k))
    sign * fac_term * A258667_inner_sum n k

lemma A258667_eq_natAbs_signed (n : ℕ) : A258667 n = (A258667_signed_sum n).natAbs := by
  by_cases h : n ≤ 5
  · simp [A258667, A258667_signed_sum, h]
  · simp [A258667, A258667_signed_sum, h]

lemma tsum_norm_summand_eq (n : ℕ) (hn : 6 ≤ n) :
    (∑' k : ℕ, A258667_norm_summand n k) =
      ((A258667_signed_sum n : ℤ) : ℝ) / (Nat.factorial (n - 1) : ℝ) := by
  have hn5 : ¬ n ≤ 5 := by omega
  have htsum : (∑' k : ℕ, A258667_norm_summand n k) =
      ∑ k ∈ Finset.range n, A258667_norm_summand n k := by
    exact tsum_eq_sum (s := Finset.range n) (by
      intro k hk
      have hkn : ¬ k < n := by simpa [Finset.mem_range] using hk
      simp [A258667_norm_summand, hn5, hkn])
  rw [htsum]
  simp [A258667_signed_sum, hn5, A258667_norm_summand]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := by simpa [Finset.mem_range] using hk
  have hk_le : k ≤ n - 1 := by omega
  simp [hkn]
  by_cases hpar : k % 2 = 0
  · have hpow : (-1 : ℝ) ^ k = 1 := by
      rw [neg_one_pow_eq_pow_mod_two, hpar]
      norm_num
    simp [hpar, hpow]
    ring
  · have hmod : k % 2 = 1 := by
      have hlt : k % 2 < 2 := Nat.mod_lt k (by norm_num)
      omega
    have hpow : (-1 : ℝ) ^ k = -1 := by
      rw [neg_one_pow_eq_pow_mod_two, hmod]
      norm_num
    simp [hpar, hpow]
    ring

lemma A258667_normalized_tendsto :
    Tendsto (fun n : ℕ => (A258667 n : ℝ) / (Nat.factorial (n - 1) : ℝ)) atTop
      (𝓝 (Real.exp (-2))) := by
  have hT : Tendsto (fun n : ℕ => ∑' k : ℕ, A258667_norm_summand n k) atTop
      (𝓝 (Real.exp (-2))) := by
    have hdc := tendsto_tsum_of_dominated_convergence
      (α := ℕ) (β := ℕ) (G := ℝ) (𝓕 := atTop)
      (f := fun n k => A258667_norm_summand n k)
      (g := fun k => (-2 : ℝ)^k / (Nat.factorial k : ℝ))
      (bound := A258667_bound)
      summable_A258667_bound norm_summand_tendsto norm_summand_le_bound
    have hsum : (∑' k : ℕ, (-2 : ℝ)^k / (Nat.factorial k : ℝ)) = Real.exp (-2) := by
      simpa [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (-2 : ℝ)).tsum_eq
    simpa [hsum] using hdc
  have habs := hT.abs
  have hposabs : |Real.exp (-2)| = Real.exp (-2) := abs_of_pos (Real.exp_pos _)


  rw [hposabs] at habs
  refine habs.congr' ?_
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hfacpos : 0 < (Nat.factorial (n - 1) : ℝ) := by positivity
  rw [tsum_norm_summand_eq n hn]
  rw [A258667_eq_natAbs_signed]
  rw [Int.cast_natAbs, Int.cast_abs]
  rw [abs_div]
  rw [abs_of_pos hfacpos]


noncomputable def asym_sum_summand (n k : ℕ) : ℝ :=
  if k < n then
    if k = 0 then 0 else
      let denom := menage_denom_term n k
      if denom = 0 then 0 else ((-1 : ℝ) ^ k) / denom
  else 0

lemma asym_sum_summand_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => asym_sum_summand n k) atTop (𝓝 (0 : ℝ)) := by
  by_cases hk0 : k = 0
  · simp [asym_sum_summand, hk0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hdesc_atTop : Tendsto (fun n : ℕ => (((n - 1).descFactorial k : ℕ) : ℝ)) atTop atTop := by
      exact (desc_shift_equiv k).symm.tendsto_atTop ((tendsto_pow_atTop (α := ℝ) hk0).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hden_atTop : Tendsto (fun n : ℕ => (Nat.factorial k : ℝ) * (((n - 1).descFactorial k : ℕ) : ℝ)) atTop atTop := by
      exact hdesc_atTop.const_mul_atTop (by positivity : 0 < (Nat.factorial k : ℝ))
    have hinv : Tendsto (fun n : ℕ => (((Nat.factorial k : ℝ) * (((n - 1).descFactorial k : ℕ) : ℝ))⁻¹)) atTop (𝓝 (0 : ℝ)) :=
      hden_atTop.inv_tendsto_atTop
    have hmain : Tendsto (fun n : ℕ => ((-1 : ℝ)^k) * (((Nat.factorial k : ℝ) * (((n - 1).descFactorial k : ℕ) : ℝ))⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      simpa using (hinv.const_mul ((-1 : ℝ)^k))
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 (k+1))] with n hn
    have hkn : k < n := by omega
    have hk_le : k ≤ n - 1 := by omega
    have hdescpos : 0 < (n - 1).descFactorial k := Nat.descFactorial_pos.mpr hk_le
    have hden_ne : menage_denom_term n k ≠ 0 := by
      dsimp [menage_denom_term, nat_fac_to_real]
      positivity
    simp [asym_sum_summand, hkn, hk0, hden_ne, menage_denom_term, nat_fac_to_real,
      Nat.factorial_ne_zero, not_lt.mpr hk_le]
    ring

lemma asym_sum_summand_bound :
    ∀ᶠ n in atTop, ∀ k, ‖asym_sum_summand n k‖ ≤ (1 : ℝ) / (Nat.factorial k : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn k
  by_cases hkn : k < n
  · by_cases hk0 : k = 0
    · simp [asym_sum_summand, hkn, hk0]
    · have hk_le : k ≤ n - 1 := by omega
      have hdescpos : 0 < (n - 1).descFactorial k := Nat.descFactorial_pos.mpr hk_le
      have hdenpos : 0 < menage_denom_term n k := by
        dsimp [menage_denom_term, nat_fac_to_real]
        positivity
      have hden_ne : menage_denom_term n k ≠ 0 := ne_of_gt hdenpos
      simp [asym_sum_summand, hkn, hk0, hden_ne]
      rw [abs_of_pos hdenpos]
      dsimp [menage_denom_term, nat_fac_to_real] at hdenpos ⊢
      rw [inv_le_inv₀ (by positivity : 0 < (Nat.factorial k : ℝ) * (((n - 1).descFactorial k : ℕ) : ℝ)) (by positivity : 0 < (Nat.factorial k : ℝ))]
      nlinarith [show (1 : ℝ) ≤ (((n - 1).descFactorial k : ℕ) : ℝ) by
        have h1 : 1 ≤ (n - 1).descFactorial k := Nat.succ_le_of_lt hdescpos
        exact_mod_cast h1]
  · simp [asym_sum_summand, hkn]

lemma A258667_asymptotic_sum_part_tendsto_zero :
    Tendsto A258667_asymptotic_sum_part atTop (𝓝 (0 : ℝ)) := by
  have hdc := tendsto_tsum_of_dominated_convergence
    (α := ℕ) (β := ℕ) (G := ℝ) (𝓕 := atTop)
    (f := fun n k => asym_sum_summand n k) (g := fun _ => (0 : ℝ))
    (bound := fun k => (1 : ℝ) / (Nat.factorial k : ℝ))
    (by simpa using (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).summable)
    asym_sum_summand_tendsto_zero asym_sum_summand_bound
  have hzero : (∑' _k : ℕ, (0 : ℝ)) = 0 := tsum_zero
  have hcongr : (fun n : ℕ => ∑' k : ℕ, asym_sum_summand n k) =ᶠ[atTop] A258667_asymptotic_sum_part := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [tsum_eq_sum (s := Finset.range n)]
    · apply Finset.sum_congr rfl
      intro k hk
      have hkn : k < n := by simpa [Finset.mem_range] using hk
      simp [A258667_asymptotic_sum_part, asym_sum_summand, hkn]
    · intro k hk
      have hkn : ¬ k < n := by simpa [Finset.mem_range] using hk
      simp [asym_sum_summand, hkn]
  simpa [hzero] using hdc.congr' hcongr

lemma A258667_asymptotic_normalized_tendsto :
    Tendsto (fun n : ℕ => A258667_asymptotic_term n / (Nat.factorial (n - 1) : ℝ)) atTop
      (𝓝 (Real.exp (-2))) := by
  have hcorr : Tendsto (fun n : ℕ => (1 : ℝ) + A258667_asymptotic_sum_part n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add A258667_asymptotic_sum_part_tendsto_zero
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 2)) atTop (𝓝 (1 : ℝ)) := by
    have ht := tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) (-2 : ℝ) (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using ht
  have hprod : Tendsto (fun n : ℕ => Real.exp (-2) * ((n : ℝ) / ((n : ℝ) - 2)) * (1 + A258667_asymptotic_sum_part n)) atTop
      (𝓝 (Real.exp (-2) * 1 * 1)) := by
    exact (tendsto_const_nhds.mul hratio).mul hcorr
  have hprod' : Tendsto (fun n : ℕ => Real.exp (-2) * ((n : ℝ) / ((n : ℝ) - 2)) * (1 + A258667_asymptotic_sum_part n)) atTop
      (𝓝 (Real.exp (-2))) := by simpa using hprod
  refine hprod'.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn2 : ¬ n ≤ 2 := by omega
  have hfac : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by positivity
  have hnsub : (n : ℝ) - 2 ≠ 0 := by
    have hn2' : (n : ℝ) ≠ 2 := by exact_mod_cast (by omega : n ≠ 2)
    exact sub_ne_zero.mpr hn2'
  simp [A258667_asymptotic_term, hn2, nat_fac_to_real]
  have hfact : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    have hnpos : 0 < n := by omega
    cases n with
    | zero => omega
    | succ m =>
        simp [Nat.factorial_succ, Nat.succ_eq_add_one]
  rw [hfact]
  field_simp [hfac, hnsub]


/--
A258667 Conjecture:
Therefore, it is natural to conjecture that a(n) ~ e^(-2)*n!/(n-2)*(1 + Sum_{k>=1} (-1)^k/(k!(n-1)_k)).
-/
theorem oeis_A258667_conjecture_0 :
  IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) A258667_asymptotic_term := by
  let F : ℕ → ℝ := fun n => (Nat.factorial (n - 1) : ℝ)
  have hcne : Real.exp (-2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hden_norm_ne : ∀ᶠ n : ℕ in atTop, A258667_asymptotic_term n / F n ≠ 0 :=
    A258667_asymptotic_normalized_tendsto.eventually_ne hcne
  have hden_ne : ∀ᶠ n : ℕ in atTop, A258667_asymptotic_term n ≠ 0 := by
    filter_upwards [hden_norm_ne] with n hn
    intro hzero
    apply hn
    simp [F, hzero]
  rw [Asymptotics.isEquivalent_iff_tendsto_one hden_ne]
  have hratio : Tendsto (fun n : ℕ =>
      ((A258667 n : ℝ) / F n) / (A258667_asymptotic_term n / F n)) atTop (𝓝 (1 : ℝ)) := by
    have h := A258667_normalized_tendsto.div A258667_asymptotic_normalized_tendsto hcne
    simpa using h
  refine hratio.congr' ?_
  filter_upwards [hden_ne] with n hn
  have hF : F n ≠ 0 := by
    dsimp [F]
    positivity
  dsimp
  field_simp [hF, hn]
