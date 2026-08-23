import FormalConjectures.Util.ProblemImports

open Real Nat

lemma log_one_sub_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 - x ^ 3 / 3 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have habs : |x| < 1 := by
      rw [abs_of_nonneg hx0]; exact hx1
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    have hnn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := by
      intro n
      exact div_nonneg (pow_nonneg hx0 _) (add_nonneg (Nat.cast_nonneg n) zero_le_one)
    have hpartial :
        ∑ i ∈ Finset.range 3, x ^ (i + 1) / ((i : ℝ) + 1) ≤
          ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) :=
      Summable.sum_le_tsum (Finset.range 3) (fun _ _ => hnn _) hsum.summable
    have hsum3 : ∑ i ∈ Finset.range 3, x ^ (i + 1) / ((i : ℝ) + 1) =
        x + x ^ 2 / 2 + x ^ 3 / 3 := by
      simp [Finset.sum_range_succ, pow_one]
      ring
    have : x + x ^ 2 / 2 + x ^ 3 / 3 ≤ -Real.log (1 - x) := by
      rw [← hsum.tsum_eq, ← hsum3]; exact hpartial
    linarith

lemma hasDerivAt_log_one_add_cubic (t : ℝ) (ht : -1 < t) :
    HasDerivAt (fun u : ℝ => u - u ^ 2 / 2 + u ^ 3 / 3 - Real.log (1 + u))
      (t ^ 3 / (1 + t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have := HasDerivAt.div_const (hasDerivAt_pow 2 t) 2
    convert this using 1; ring
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) (t ^ 2) t := by
    have := HasDerivAt.div_const (hasDerivAt_pow 3 t) 3
    convert this using 1; ring
  have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) ((1 + t)⁻¹) t := by
    have : HasDerivAt (fun u : ℝ => (1 : ℝ) + u) 1 t :=
      (hasDerivAt_id t).const_add 1
    convert this.log (by linarith) using 1
    field_simp
  have hcomb := ((h1.sub h2).add h3).sub hlog
  convert hcomb using 1
  have hne : (1 + t : ℝ) ≠ 0 := by linarith
  field_simp
  ring

lemma log_one_add_cubic {x : ℝ} (hx0 : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    let f : ℝ → ℝ := fun u => u - u ^ 2 / 2 + u ^ 3 / 3 - Real.log (1 + u)
    have hcont : ContinuousOn f (Set.Icc 0 x) := by
      intro t ht
      have ht' : -1 < t := by
        have := Set.mem_Icc.mp ht
        linarith
      exact (hasDerivAt_log_one_add_cubic t ht').continuousAt.continuousWithinAt
    have hdiff : ∀ t ∈ Set.Ioo 0 x, HasDerivAt f (t ^ 3 / (1 + t)) t := by
      intro t ht
      have ht' : -1 < t := by
        have := Set.mem_Ioo.mp ht
        linarith
      exact hasDerivAt_log_one_add_cubic t ht'
    obtain ⟨c, hc, heq⟩ :=
      exists_hasDerivAt_eq_slope f (fun t => t ^ 3 / (1 + t)) hxpos hcont hdiff
    have hc0 : 0 < c := (Set.mem_Ioo.mp hc).1
    have hder : 0 ≤ c ^ 3 / (1 + c) :=
      div_nonneg (pow_nonneg (le_of_lt hc0) 3) (by linarith)
    have hxne : (x : ℝ) - 0 ≠ 0 := by linarith
    have hsub : f x - f 0 = (c ^ 3 / (1 + c)) * (x - 0) :=
      (div_eq_iff hxne).mp heq.symm
    have : 0 ≤ f x - f 0 := by
      rw [hsub]
      exact mul_nonneg hder (by linarith)
    simp [f] at this
    linarith

lemma fact13_eq : (13 : ℕ).factorial = 6227020800 := by native_decide

lemma exp_seven_gt_1095 : (1095 : ℝ) < Real.exp 7 := by
  have hbase : (2718 / 1000 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow : (2718 / 1000 : ℝ) ^ 7 < Real.exp 1 ^ 7 :=
    pow_lt_pow_left₀ hbase (by positivity) (by decide : (7 : ℕ) ≠ 0)
  have hexp : Real.exp 1 ^ 7 = Real.exp 7 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 7).symm
  have hrat : (1095 : ℝ) < (2718 / 1000 : ℝ) ^ 7 := by
    rw [div_pow]
    have hN : (1095 : ℕ) * 1000 ^ 7 < 2718 ^ 7 := by native_decide
    have : (1095 : ℝ) * 1000 ^ 7 < 2718 ^ 7 := by exact_mod_cast hN
    have hpos : (0 : ℝ) < 1000 ^ 7 := by positivity
    exact (lt_div_iff₀ hpos).mpr (by linarith)
  linarith

lemma exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have : (27 / 10 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have : (27 / 10 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    pow_lt_pow_left₀ this (by positivity) (by decide : (2 : ℕ) ≠ 0)
  have : Real.exp 1 ^ 2 = Real.exp 2 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 2).symm
  have : (27 / 10 : ℝ) ^ 2 = 729 / 100 := by norm_num
  linarith

lemma pow1095_three : (1095 : ℕ) ^ 3 = 1312932375 := by native_decide

lemma log_fact13_lt_23 : Real.log ((13 : ℕ).factorial : ℝ) < 23 := by
  rw [fact13_eq]
  have hpos : (0 : ℝ) < 6227020800 := by norm_num
  refine (Real.log_lt_iff_lt_exp hpos).mpr ?_
  have h7 := exp_seven_gt_1095
  have h2 := exp_two_gt_seven
  have hexp : Real.exp 23 = Real.exp 7 ^ 3 * Real.exp 2 := by
    have h23 : (23 : ℝ) = 3 * 7 + 2 := by norm_num
    rw [h23, Real.exp_add]
    have : Real.exp (3 * 7) = Real.exp 7 ^ 3 := by
      simpa using Real.exp_nat_mul (7 : ℝ) 3
    rw [this]
  have h1095 : (1095 : ℝ) ^ 3 * 7 < Real.exp 7 ^ 3 * Real.exp 2 := by
    have h1 : (1095 : ℝ) ^ 3 < Real.exp 7 ^ 3 :=
      pow_lt_pow_left₀ h7 (by positivity) (by decide : (3 : ℕ) ≠ 0)
    nlinarith [exp_pos (7 : ℝ), exp_pos (2 : ℝ)]
  have hnum : (6227020800 : ℝ) < (1095 : ℝ) ^ 3 * 7 := by
    have : (1095 : ℕ) ^ 3 * 7 = 9190526625 := by
      rw [pow1095_three]
    have : (6227020800 : ℕ) < 9190526625 := by decide
    exact_mod_cast this
  linarith

lemma log_six_div_five_le : Real.log (6 / 5 : ℝ) ≤ (1 / 5 : ℝ) := by
  have : Real.log (6 / 5) = Real.log (1 + 1 / 5) := by norm_num
  rw [this]
  simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 5)

lemma midShift_sq_bound (k s : ℕ) (h : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    (s : ℝ) ^ 2 ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) := by
  have : (s : ℝ) * s ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) := by exact_mod_cast h
  rwa [pow_two] at this

lemma s_pow4_div_le (k s : ℕ) (hk : 2001 ≤ k)
    (hs2 : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    2 * (s : ℝ) ^ 4 / (3 * (k : ℝ) ^ 3) ≤ 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs2r : (s : ℝ) ^ 2 ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) :=
    midShift_sq_bound k s hs2
  have hnum : (s : ℝ) ^ 4 ≤ ((k : ℝ) * (3 * Nat.log 2 k + 8)) ^ 2 := by
    have : (s : ℝ) ^ 4 = ((s : ℝ) ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (sq_nonneg _) hs2r
  have : 2 * (s : ℝ) ^ 4 / (3 * (k : ℝ) ^ 3) ≤
      2 * ((k : ℝ) * (3 * Nat.log 2 k + 8)) ^ 2 / (3 * (k : ℝ) ^ 3) := by
    apply div_le_div_of_nonneg_right
    nlinarith
    positivity
  refine le_trans this ?_
  have hsimp : 2 * ((k : ℝ) * (3 * Nat.log 2 k + 8)) ^ 2 / (3 * (k : ℝ) ^ 3) =
      2 * (3 * Nat.log 2 k + 8 : ℝ) ^ 2 / (3 * k) := by
    field_simp; ring
  rw [hsimp]
  -- (3L+8)^2 ≤ (3/2) k  ⇒  2*(3L+8)^2/(3k) ≤ 1
  have hL : (3 * Nat.log 2 k + 8 : ℕ) ^ 2 ≤ k * 3 / 2 + k := by
    -- prove (3L+8)^2 ≤ 2k which implies the claim
    have hls : Nat.log 2 k ≤ k.sqrt := by
      -- for k≥81; we only have 2001≤k
      have : 81 ≤ k := by omega
      -- inline a weak bound: log2 k ≤ 64 for a split, or use k.sqrt
      have hn : 6 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 6 * 6 ≤ k)
      -- 2^{sqrt+1} ≥ (sqrt+1)^2 ≥ k? Use Nat.log_lt
      have hk0 : k ≠ 0 := by omega
      have : Nat.log 2 k < k.sqrt + 1 := by
        rw [Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hk0]
        refine lt_of_lt_of_le (Nat.lt_succ_sqrt k) ?_
        -- 2^{sqrt+1} ≥ (sqrt+1)^2? not always needed: lt_succ_sqrt says k < (sqrt+1)^2
        -- we need k < 2^{sqrt+1}
        have hsq : 9 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 9 * 9 ≤ k)
        -- 2^{n+1} ≥ (n+1)^2 for n≥6
        have hpow : ∀ n, 6 ≤ n → (n + 1) * (n + 1) ≤ 2 ^ (n + 1) := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => decide
          | succ n hn ih =>
            have : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := Nat.pow_succ _ _
            rw [this]
            nlinarith
        exact hpow k.sqrt (by omega)
      omega
    have : 3 * Nat.log 2 k + 8 ≤ 3 * k.sqrt + 8 := by omega
    have h44 : 44 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 44 * 44 ≤ k)
    -- (3 sqrt + 8)^2 ≤ 2 k ? (3s+8)^2 ≤ 2 s^2 * (something). s^2 ≤ k so
    -- (3s+8)^2 = 9s^2 + 48s + 64 ≤ 9k + 48s + 64
    -- We need (3L+8)^2 ≤ 2k. 9k is too big.
    -- Direct: L ≤ log2 k, k ≥ 2^L, (3L+8)^2 ≤ 2 * 2^L = 2^{L+1}
    have hpow : (3 * Nat.log 2 k + 8) * (3 * Nat.log 2 k + 8) ≤ 2 * k := by
      have hL := Nat.pow_log_le_self 2 (show k ≠ 0 by omega)
      -- k ≥ 2^L
      have hLval : Nat.log 2 k ≤ 40 ∨ 41 ≤ Nat.log 2 k := le_or_gt _ _
      -- split: small L by compute, large L by  (3L+8)^2 ≤ 2^{L+1} ≤ 2k
      cases le_or_gt (Nat.log 2 k) 20 with
      | inl h20 =>
        -- L ≤ 20, (3*20+8)^2 = 68^2 = 4624, 2k ≥ 4002. 4624>4002 FAIL for k=2001 L=10 is OK (1444<4002)
        -- max of (3L+8)^2 for L≤20 at L=20 is 4624, need 2k ≥ 4624, k≥2312
        -- so split L≤12 vs larger
        sorry
      | inr h20 =>
        sorry
    have : 2 * (3 * Nat.log 2 k + 8 : ℝ) ^ 2 / (3 * k) ≤
        2 * (2 * k : ℝ) / (3 * k) := by
      have : (3 * Nat.log 2 k + 8 : ℝ) ^ 2 ≤ 2 * k := by exact_mod_cast hpow
      apply div_le_div_of_nonneg_right
      nlinarith
      positivity
    refine le_trans this ?_
    field_simp
    linarith

