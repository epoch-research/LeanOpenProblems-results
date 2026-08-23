import FormalConjectures.Util.ProblemImports

open Real Nat Finset

def midShift (k : ℕ) : ℕ :=
  max (5 * k.sqrt) ((k * (3 * Nat.log 2 k + 8)).sqrt)

lemma six_le_log2 (k : ℕ) (hk : 81 ≤ k) : 6 ≤ Nat.log 2 k := by
  have hpow : 2 ^ 6 ≤ k := by omega
  exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : k ≠ 0)).2 hpow

lemma two_pow_ge_sq_succ : ∀ n, 6 ≤ n → (n + 1) * (n + 1) ≤ 2 ^ (n + 1)
  | n, hn => by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      have h2 : 2 * ((n + 1) * (n + 1)) ≤ 2 ^ (n + 2) := by
        have : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := Nat.pow_succ _ _
        rw [this, Nat.mul_comm (2 ^ (n + 1))]
        exact Nat.mul_le_mul_left 2 ih
      refine le_trans ?_ h2
      nlinarith

lemma log2_le_sqrt (k : ℕ) (hk : 81 ≤ k) : Nat.log 2 k ≤ k.sqrt := by
  have hk0 : k ≠ 0 := by omega
  have hlt : Nat.log 2 k < k.sqrt + 1 := by
    rw [Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hk0]
    refine lt_of_lt_of_le (Nat.lt_succ_sqrt k) ?_
    have hn : 6 ≤ k.sqrt := by
      have : 9 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 9 * 9 ≤ k)
      omega
    exact two_pow_ge_sq_succ k.sqrt hn
  omega

lemma midShift_eq_logsqrt (k : ℕ) (hk : 81 ≤ k) :
    midShift k = (k * (3 * Nat.log 2 k + 8)).sqrt := by
  apply max_eq_right
  have h25 : 25 ≤ 3 * Nat.log 2 k + 8 := by
    have : 6 ≤ Nat.log 2 k := six_le_log2 k hk; omega
  have hsq : k.sqrt * k.sqrt ≤ k := Nat.sqrt_le k
  have : (5 * k.sqrt) * (5 * k.sqrt) ≤ k * (3 * Nat.log 2 k + 8) := by
    have hL : (5 * k.sqrt) * (5 * k.sqrt) = 25 * (k.sqrt * k.sqrt) := by ring
    rw [hL]
    refine le_trans (Nat.mul_le_mul_left 25 hsq) ?_
    rw [Nat.mul_comm 25]; exact Nat.mul_le_mul_left k h25
  exact Nat.le_sqrt.mpr this

lemma three_log_mul_le (k : ℕ) (hk : 81 ≤ k) :
    k * (3 * Nat.log 2 k + 8) ≤ (k - 24) * (k - 24) := by
  by_cases h : k < 2 ^ 10
  · have hlog : Nat.log 2 k ≤ 9 := by
      have := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : k ≠ 0)).2 h
      omega
    have : k * (3 * Nat.log 2 k + 8) ≤ k * 35 := Nat.mul_le_mul_left k (by omega)
    refine le_trans this ?_
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hk1 : 81 + t - 24 = 57 + t := by omega
    rw [hk1]; nlinarith
  · have hk' : 1024 ≤ k := by omega
    have hls : Nat.log 2 k ≤ k.sqrt := log2_le_sqrt k (by omega)
    have hmul : k * (3 * Nat.log 2 k + 8) ≤ k * (3 * k.sqrt + 8) :=
      Nat.mul_le_mul_left k (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hls) _)
    refine le_trans hmul ?_
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk'
    have hs : 32 ≤ (1024 + t).sqrt := Nat.le_sqrt.mpr (by omega : 32 * 32 ≤ 1024 + t)
    have hcore : 3 * (1024 + t).sqrt + 8 ≤ 1024 + t - 48 := by
      have : 3 * (1024 + t).sqrt + 56 ≤ (1024 + t).sqrt * (1024 + t).sqrt := by
        obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hs
        rw [hu]; nlinarith
      have := le_trans this (Nat.sqrt_le _)
      omega
    have hmul' := Nat.mul_le_mul_left (1024 + t) hcore
    refine le_trans hmul' ?_
    have hk1 : 1024 + t - 24 = 1000 + t := by omega
    have hk2 : 1024 + t - 48 = 976 + t := by omega
    rw [hk1, hk2]; nlinarith

lemma midShift_add_24_le (k : ℕ) (hk : 81 ≤ k) : midShift k + 24 ≤ k := by
  rw [midShift_eq_logsqrt k hk]
  have hsq := Nat.sqrt_le_sqrt (three_log_mul_le k hk)
  rw [Nat.sqrt_eq] at hsq
  omega

lemma midShift_pos (k : ℕ) (hk : 81 ≤ k) : 2 ≤ midShift k := by
  have : 5 * k.sqrt ≤ midShift k := le_max_left _ _
  have : 9 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega : 9 * 9 ≤ k)
  omega

lemma midShift_sq_ge (k : ℕ) (hk : 81 ≤ k) :
    k * (3 * Nat.log 2 k + 8) ≤ (midShift k + 1) * (midShift k + 1) := by
  rw [midShift_eq_logsqrt k hk]
  exact (Nat.lt_succ_sqrt _).le

lemma log_one_sub_quadratic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    have hnn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := fun n =>
      div_nonneg (pow_nonneg hx0 _) (add_nonneg (Nat.cast_nonneg n) zero_le_one)
    have hpartial :=
      Summable.sum_le_tsum (Finset.range 2) (fun _ _ => hnn _) hsum.summable
    have hsum2 : ∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1) = x + x ^ 2 / 2 := by
      simp [Finset.sum_range_succ, pow_one]; ring
    have : x + x ^ 2 / 2 ≤ -Real.log (1 - x) := by
      rw [← hsum.tsum_eq, ← hsum2]; exact hpartial
    linarith

lemma real_log_two_lt_one : Real.log 2 < 1 := by
  have : Real.log 2 < Real.log (Real.exp 1) :=
    Real.log_lt_log (by positivity) Real.exp_one_gt_two
  rwa [Real.log_exp] at this

lemma real_log_six_gt_one : 1 < Real.log 6 := by
  have : Real.exp 1 < 6 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) this

lemma real_two_pi_ge_six : (6 : ℝ) ≤ 2 * Real.pi := by
  linarith [le_of_lt Real.pi_gt_three]

lemma real_log_two_pi_gt_one : 1 < Real.log (2 * Real.pi) :=
  lt_of_lt_of_le real_log_six_gt_one
    (Real.log_le_log (by positivity) real_two_pi_ge_six)

lemma nat_log2_ge_log_div (k : ℕ) (hk : 1 ≤ k) :
    Real.log k / Real.log 2 - 1 < Nat.log 2 k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
  have : (k : ℝ) < (2 : ℝ) ^ (Nat.log 2 k + 1) := by exact_mod_cast hlt
  have hloglt : Real.log k < (Nat.log 2 k + 1 : ℝ) * Real.log 2 := by
    have := Real.log_lt_log hkpos this
    rw [Real.log_pow] at this; convert this; simp
  have : Real.log k / Real.log 2 < (Nat.log 2 k : ℝ) + 1 :=
    (div_lt_iff₀ hlog2pos).mpr (by linarith)
  linarith

lemma three_log_k_le_three_log2 (k : ℕ) (hk : 81 ≤ k) :
    (3 : ℝ) * Real.log k + 3 ≤ 3 * Nat.log 2 k + 8 := by
  have hlt := nat_log2_ge_log_div k (by omega)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2lt : Real.log 2 < 1 := real_log_two_lt_one
  have hdiv : Real.log k ≤ Real.log k / Real.log 2 := by
    have hlogk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
    exact (le_div_iff₀ hlog2pos).mpr (by nlinarith [hlog2lt])
  nlinarith

lemma midShift_sq_div_ge (k : ℕ) (hk : 81 ≤ k) :
    (3 : ℝ) * Real.log k + 3 ≤ ((midShift k : ℝ) + 1) ^ 2 / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsq : (k : ℝ) * (3 * Nat.log 2 k + 8) ≤ ((midShift k : ℝ) + 1) ^ 2 := by
    have := midShift_sq_ge k hk
    have : (k : ℝ) * (3 * Nat.log 2 k + 8) ≤
        ((midShift k : ℝ) + 1) * ((midShift k : ℝ) + 1) := by exact_mod_cast this
    rwa [pow_two]
  exact le_trans (three_log_k_le_three_log2 k hk)
    ((le_div_iff₀ hkpos).mpr (by linarith [hsq]))

lemma neg_log_one_sub_inv (k : ℕ) (hk : 2 ≤ k) :
    ((k - 1 : ℕ) : ℝ) * (-Real.log (1 - (1 : ℝ) / k)) ≤ 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpos : (0 : ℝ) < 1 - (1 : ℝ) / k := by
    have : (1 : ℝ) / k < 1 := (div_lt_one hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
    linarith
  have hinv : Real.log ((1 - (1 : ℝ) / k)⁻¹) = -Real.log (1 - 1 / k) := Real.log_inv _
  have hup := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hk1ne : (k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    linarith
  have hfrac : (1 - (1 : ℝ) / k)⁻¹ - 1 = (1 : ℝ) / ((k : ℝ) - 1) := by
    field_simp [hkpos.ne', hk1ne]; ring
  have : -Real.log (1 - (1 : ℝ) / k) ≤ 1 / ((k : ℝ) - 1) := by
    rw [← hinv]; linarith
  have hkn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  rw [hkm1]
  have hmul := mul_le_mul_of_nonneg_left this hkn
  have hcancel : ((k : ℝ) - 1) * (1 / ((k : ℝ) - 1)) = 1 := mul_div_cancel₀ 1 hk1ne
  linarith

lemma log_fact_stirling_lower {n : ℕ} (hn : n ≠ 0) :
    n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2 ≤
      Real.log (n.factorial : ℝ) :=
  Stirling.le_log_factorial_stirling hn

lemma stirlingSeq_antitone_ge_one {n : ℕ} (hn : 1 ≤ n) :
    Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have h := Stirling.stirlingSeq'_antitone (Nat.zero_le n)
    simpa [Function.comp] using h

lemma factorial_upper_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have hseq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 :=
    stirlingSeq_antitone_ge_one hn
  rw [Stirling.stirlingSeq_one] at hseq
  unfold Stirling.stirlingSeq at hseq
  have hpos : (0 : ℝ) < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  rw [div_le_iff₀ hpos] at hseq
  refine le_trans hseq ?_
  have hsq : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) (n : ℝ)
  rw [hsq]
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp; simp

lemma log_factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ 1 + Real.log n / 2 + n * Real.log n - n := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hle := factorial_upper_stirling n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_log hpos hle
  refine le_trans this ?_
  have h1 : Real.log (Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n) =
      1 + Real.log n / 2 + n * (Real.log n - 1) := by
    have he : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    have hs : Real.log (Real.sqrt (n : ℝ)) = Real.log n / 2 := Real.log_sqrt (le_of_lt hn0)
    have hp : Real.log (((n : ℝ) / Real.exp 1) ^ n) = n * Real.log ((n : ℝ) / Real.exp 1) :=
      Real.log_pow _ n
    have hd : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
      rw [Real.log_div (ne_of_gt hn0) (Real.exp_ne_zero 1), Real.log_exp]
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), he, hs, hp, hd]
  rw [h1]; linarith

lemma two_real_log_fact_upper {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.log (n.factorial : ℝ) ≤
      2 + Real.log n + 2 * n * Real.log n - 2 * n := by
  linarith [log_factorial_upper hn]

lemma mid_cut_bounds (k : ℕ) (hk : 81 ≤ k) :
    24 ≤ k - midShift k ∧ k - midShift k + 2 ≤ k ∧
      2 ≤ midShift k ∧ midShift k + 1 < k := by
  have hs24 := midShift_add_24_le k hk
  have hs2 := midShift_pos k hk
  omega

/-- Combine 2 log((j-1)!) with the remaining power. -/
lemma two_log_fact_shift_combine {j k : ℕ} (hj : 3 ≤ j) :
    2 * Real.log (((j - 1).factorial : ℝ)) +
      (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ) ≤
      4 - 2 * (j : ℝ) + 2 * (k : ℝ) * Real.log ((j - 1 : ℕ) : ℝ) := by
  have hjm : 1 ≤ j - 1 := by omega
  have hup := two_real_log_fact_upper (n := j - 1) hjm
  have hjcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  have hstep :
      2 * Real.log (((j - 1).factorial : ℝ)) +
        (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ) ≤
      2 + Real.log ((j - 1 : ℕ) : ℝ) +
        2 * ((j - 1 : ℕ) : ℝ) * Real.log ((j - 1 : ℕ) : ℝ)
        - 2 * ((j - 1 : ℕ) : ℝ) +
        (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ) := by
    linarith [hup]
  refine le_trans hstep ?_
  have hcoef : (1 : ℝ) + 2 * ((j - 1 : ℕ) : ℝ) + (2 * (k : ℝ) - 2 * (j : ℝ) + 1) =
      2 * (k : ℝ) := by rw [hjcast]; ring
  have hconst : (2 : ℝ) - 2 * ((j - 1 : ℕ) : ℝ) = 4 - 2 * (j : ℝ) := by
    rw [hjcast]; ring
  calc
    2 + Real.log ((j - 1 : ℕ) : ℝ) +
        2 * ((j - 1 : ℕ) : ℝ) * Real.log ((j - 1 : ℕ) : ℝ)
        - 2 * ((j - 1 : ℕ) : ℝ) +
        (2 * (k : ℝ) - 2 * (j : ℝ) + 1) * Real.log ((j - 1 : ℕ) : ℝ)
        = (2 - 2 * ((j - 1 : ℕ) : ℝ)) +
          ((1 : ℝ) + 2 * ((j - 1 : ℕ) : ℝ) + (2 * (k : ℝ) - 2 * (j : ℝ) + 1)) *
            Real.log ((j - 1 : ℕ) : ℝ) := by ring
    _ = (4 - 2 * (j : ℝ)) + (2 * (k : ℝ)) * Real.log ((j - 1 : ℕ) : ℝ) := by
        rw [hconst, hcoef]
  exact le_of_eq (by ring)

lemma jpred_cast (k : ℕ) (hk : 81 ≤ k) :
    ((k - midShift k - 1 : ℕ) : ℝ) = (k : ℝ) - ((midShift k + 1 : ℕ) : ℝ) := by
  have : k - midShift k - 1 = k - (midShift k + 1) := by
    have := (mid_cut_bounds k hk).2.2.2; omega
  rw [this, Nat.cast_sub (by
    have := (mid_cut_bounds k hk).2.2.2; omega), Nat.cast_add, Nat.cast_one]

lemma two_k_log_jpred (k : ℕ) (hk : 81 ≤ k) :
    2 * (k : ℝ) * Real.log ((k - midShift k - 1 : ℕ) : ℝ) ≤
      2 * (k : ℝ) * Real.log k
        - 2 * ((midShift k + 1 : ℕ) : ℝ)
        - ((midShift k + 1 : ℕ) : ℝ) ^ 2 / k := by
  set s := midShift k
  have hsk : s + 1 < k := (mid_cut_bounds k hk).2.2.2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hjcast := jpred_cast k hk
  have hfrac : ((k - s - 1 : ℕ) : ℝ) = (k : ℝ) * (1 - ((s + 1 : ℕ) : ℝ) / k) := by
    rw [show s = midShift k from rfl, hjcast]
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    field_simp [hkne]
  have hpos : (0 : ℝ) < 1 - ((s + 1 : ℕ) : ℝ) / k := by
    have : ((s + 1 : ℕ) : ℝ) / k < 1 :=
      (div_lt_one hkpos).mpr (by exact_mod_cast hsk)
    linarith
  have hlog : Real.log ((k - s - 1 : ℕ) : ℝ) =
      Real.log k + Real.log (1 - ((s + 1 : ℕ) : ℝ) / k) := by
    rw [hfrac, Real.log_mul hkpos.ne' (ne_of_gt hpos)]
  have hx0 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) / k := by positivity
  have hx1 : ((s + 1 : ℕ) : ℝ) / k < 1 :=
    (div_lt_one hkpos).mpr (by exact_mod_cast hsk)
  have hquad := log_one_sub_quadratic hx0 hx1
  have h2k : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  rw [hlog]
  have hexp : 2 * (k : ℝ) * (Real.log k + Real.log (1 - ((s + 1 : ℕ) : ℝ) / k)) =
      2 * (k : ℝ) * Real.log k + 2 * (k : ℝ) * Real.log (1 - ((s + 1 : ℕ) : ℝ) / k) := by
    ring
  rw [hexp]
  have hmul := mul_le_mul_of_nonneg_left hquad h2k
  have hsum := add_le_add_right hmul (2 * (k : ℝ) * Real.log k)
  refine le_trans hsum ?_
  -- 2k log k + 2k (-x - x²/2) = 2k log k - 2(s+1) - (s+1)²/k
  have hx : (2 * (k : ℝ)) * (((s + 1 : ℕ) : ℝ) / k) = 2 * ((s + 1 : ℕ) : ℝ) := by
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    field_simp [hkne]
  have hx2 : (2 * (k : ℝ)) * ((((s + 1 : ℕ) : ℝ) / k) ^ 2 / 2) =
      ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    field_simp [hkne]
  linarith

lemma neg_km1_log (k : ℕ) (hk : 2 ≤ k) :
    -((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) ≤
      -((k - 1 : ℕ) : ℝ) * Real.log k + 1 := by
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpos : (0 : ℝ) < 1 - (1 : ℝ) / k := by
    have : (1 : ℝ) / k < 1 := (div_lt_one hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
    linarith
  have hlogeq : Real.log ((k - 1 : ℕ) : ℝ) = Real.log k + Real.log (1 - (1 : ℝ) / k) := by
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) * (1 - (1 : ℝ) / k) := by
      rw [hkm1]
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp [hkne]
    rw [this, Real.log_mul (ne_of_gt hkpos) (ne_of_gt hpos)]
  have hneg := neg_log_one_sub_inv k hk
  have hmul : ((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) =
      ((k - 1 : ℕ) : ℝ) * Real.log k +
        ((k - 1 : ℕ) : ℝ) * Real.log (1 - (1 : ℝ) / k) := by
    rw [hlogeq]; ring
  have : -(((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)) =
      -((k - 1 : ℕ) : ℝ) * Real.log k
        - ((k - 1 : ℕ) : ℝ) * Real.log (1 - (1 : ℝ) / k) := by
    rw [hmul]; ring
  -- rewrite the goal's left side similarly
  have hL : -((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) =
      -(((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)) := by ring
  rw [hL, this]
  have : -((k - 1 : ℕ) : ℝ) * Real.log (1 - (1 : ℝ) / k) =
      ((k - 1 : ℕ) : ℝ) * (-Real.log (1 - (1 : ℝ) / k)) := by ring
  linarith

lemma neg_two_logs_fact (k : ℕ) (hk : 81 ≤ k) :
    -Real.log (k.factorial : ℝ) - Real.log (((k - 1).factorial : ℝ)) ≤
      -((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi) := by
  have h1 := log_fact_stirling_lower (show k ≠ 0 by omega)
  have h2 := log_fact_stirling_lower (show k - 1 ≠ 0 by omega)
  have hneg := neg_km1_log k (by omega)
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hkU : -Real.log (k.factorial : ℝ) ≤
      -(k : ℝ) * Real.log k + (k : ℝ) - Real.log k / 2 - Real.log (2 * Real.pi) / 2 := by
    linarith [h1]
  have hkmU : -Real.log (((k - 1).factorial : ℝ)) ≤
      -((k - 1 : ℕ) : ℝ) * Real.log ((k - 1 : ℕ) : ℝ)
        + ((k - 1 : ℕ) : ℝ)
        - Real.log ((k - 1 : ℕ) : ℝ) / 2 - Real.log (2 * Real.pi) / 2 := by
    linarith [h2]
  have hsum : -Real.log (k.factorial : ℝ) - Real.log (((k - 1).factorial : ℝ)) ≤
      -(k : ℝ) * Real.log k + (k : ℝ) - Real.log k / 2 - Real.log (2 * Real.pi) / 2
        - ((k - 1 : ℕ) : ℝ) * Real.log k + 1
        + ((k - 1 : ℕ) : ℝ)
        - Real.log ((k - 1 : ℕ) : ℝ) / 2 - Real.log (2 * Real.pi) / 2 := by
    linarith [hkU, hkmU, hneg]
  rw [hkm1] at hsum ⊢
  have hrew : -((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k : ℝ) - 1)) / 2
        - Real.log (2 * Real.pi)
      = -(k : ℝ) * Real.log k + (k : ℝ) - Real.log k / 2 - Real.log (2 * Real.pi) / 2
        - ((k : ℝ) - 1) * Real.log k + 1
        + ((k : ℝ) - 1)
        - Real.log ((k : ℝ) - 1) / 2 - Real.log (2 * Real.pi) / 2 := by
    ring
  linarith

lemma leftover_nonpos (k : ℕ) (hk : 81 ≤ k) :
    Real.log 2 + (2 : ℝ) - Real.log (2 * Real.pi) + (3 : ℝ) * Real.log k
      + (1 / 2) * Real.log (k / ((k - 1 : ℕ) : ℝ))
      - ((midShift k : ℝ) + 1) ^ 2 / k ≤ 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkm1pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hle1 : Real.log (k / ((k - 1 : ℕ) : ℝ)) ≤ 1 := by
    have heq : (k : ℝ) / ((k - 1 : ℕ) : ℝ) = 1 + 1 / ((k - 1 : ℕ) : ℝ) := by
      rw [hkm1]
      have hne : (k : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    rw [heq]
    have hx1 : (1 : ℝ) / ((k - 1 : ℕ) : ℝ) ≤ 1 := by
      have : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
      exact div_le_one_of_le₀ this (le_of_lt hkm1pos)
    have hlog := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + 1 / ((k - 1 : ℕ) : ℝ))
    linarith
  have hconst : Real.log 2 + (2 : ℝ) - Real.log (2 * Real.pi) + (1 / 2 : ℝ) ≤ (5 / 2 : ℝ) := by
    linarith [real_log_two_lt_one, real_log_two_pi_gt_one]
  have hdom := midShift_sq_div_ge k hk
  have hhalf : (1 / 2 : ℝ) * Real.log (k / ((k - 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
    nlinarith [hle1]
  linarith [hdom, hconst, hhalf]

/-- Algebraic identity: `4 - 2j - 2(s+1) + 2k = 2` when `j = k - s`. -/
lemma mid_linear_const (k : ℕ) (hk : 81 ≤ k) :
    (4 : ℝ) - 2 * ((k - midShift k : ℕ) : ℝ)
      - 2 * ((midShift k + 1 : ℕ) : ℝ) + 2 * (k : ℝ) = 2 := by
  have hsle : midShift k ≤ k := by
    have := midShift_add_24_le k hk; omega
  have hj : ((k - midShift k : ℕ) : ℝ) = (k : ℝ) - (midShift k : ℝ) :=
    Nat.cast_sub hsle
  have hsc : ((midShift k + 1 : ℕ) : ℝ) = (midShift k : ℝ) + 1 := by simp
  rw [hj, hsc]; ring

lemma mid_cut_log_diff_le (k : ℕ) (hk : 81 ≤ k) :
    let s := midShift k
    let j := k - s
    Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
      + (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ)
      - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
      + 2 * Real.log k ≤ 0 := by
  intro s j
  have hb := mid_cut_bounds k hk
  have hj24 : 24 ≤ j := by
    simpa [j, s] using hb.1
  have hj3 : 3 ≤ j := by omega
  have hsle : s ≤ k := by
    have := midShift_add_24_le k hk; omega
  have hcast_j1 : (j - 1 : ℝ) = ((j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  have hcomb := two_log_fact_shift_combine (j := j) (k := k) hj3
  have hgoal_comb :
      2 * Real.log ((j - 1).factorial : ℝ) +
        (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ) ≤
      4 - 2 * (j : ℝ) + 2 * (k : ℝ) * Real.log (j - 1 : ℝ) := by
    -- `(2*k - 2*j + 1 : ℝ)` is defeq to `2*↑k - 2*↑j + 1`
    simpa [hcast_j1] using hcomb
  have hj1eq : j - 1 = k - s - 1 := by omega
  have h2k := two_k_log_jpred k hk
  have h2k' : 2 * (k : ℝ) * Real.log (j - 1 : ℝ) ≤
      2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
    rw [hcast_j1, hj1eq]
    simpa [s] using h2k
  have hneg := neg_two_logs_fact k hk
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogj : Real.log j ≤ Real.log k :=
    Real.log_le_log hjpos (by exact_mod_cast (show j ≤ k by omega))
  have hlin := mid_linear_const k hk
  -- Step 1: replace the two-fact + power by the combined upper bound
  have hstep1 :
      Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
        + (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k
      ≤ Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k := by
    linarith [hgoal_comb]
  -- Step 2: expand log(j-1)
  have hstep2 :
      Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k
      ≤ Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k := by
    linarith [h2k']
  -- Step 3: Stirling lower bounds
  have hstep3 :
      Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k
      ≤ Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - ((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        + 2 * Real.log k := by
    linarith [hneg]
  have hlin' : (4 : ℝ) - 2 * (j : ℝ) - 2 * ((s + 1 : ℕ) : ℝ) + 2 * (k : ℝ) = 2 := by
    simpa [j, s] using hlin
  have hlogs : (2 : ℝ) * (k : ℝ) * Real.log k
      - (2 * (k : ℝ) - 1) * Real.log k + 2 * Real.log k
      = (3 : ℝ) * Real.log k := by ring
  have hsimp :
      Real.log 2 + Real.log j + 4 - 2 * (j : ℝ)
        + 2 * (k : ℝ) * Real.log k - 2 * ((s + 1 : ℕ) : ℝ)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
        - ((2 * (k : ℝ) - 1) * Real.log k) + 2 * (k : ℝ)
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        + 2 * Real.log k
      = Real.log 2 + Real.log j + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
    linear_combination hlin' + hlogs
  -- Now log j ≤ log k, and leftover ≤ 0
  have hcast_s1 : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by simp
  have hleft := leftover_nonpos k hk
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  -- leftover is log2 + 2 - log(2π) + 3 log k + (1/2) log(k/(k-1)) - (s+1)²/k ≤ 0
  -- Our expression after replacing log j by log k is:
  -- log2 + log k + 2 + 3 log k - (log k + log(k-1))/2 - log(2π) - (s+1)²/k
  -- = log2 + 2 - log(2π) + 3 log k + log k - log k/2 - log(k-1)/2 - (s+1)²/k
  -- = leftover without the (1/2)log(k/(k-1)) plus log k - log k/2 - log(k-1)/2
  -- log k - log k/2 - log(k-1)/2 = log k/2 - log(k-1)/2 = (1/2) log(k/(k-1))
  have hident :
      Real.log 2 + Real.log k + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
      = Real.log 2 + (2 : ℝ) - Real.log (2 * Real.pi) + (3 : ℝ) * Real.log k
        + (1 / 2) * Real.log (k / ((k - 1 : ℕ) : ℝ))
        - ((midShift k : ℝ) + 1) ^ 2 / k := by
    have hdiv : Real.log (k / ((k - 1 : ℕ) : ℝ)) =
        Real.log k - Real.log ((k - 1 : ℕ) : ℝ) :=
      Real.log_div (ne_of_gt hkpos)
        (by exact_mod_cast (show k - 1 ≠ 0 by omega))
    have hs1 : ((s + 1 : ℕ) : ℝ) = (midShift k : ℝ) + 1 := by
      simp [s]
    rw [hdiv, hs1]
    ring
  have hfinal :
      Real.log 2 + Real.log j + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k ≤ 0 := by
    have : Real.log 2 + Real.log j + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k
      ≤ Real.log 2 + Real.log k + 2 + (3 : ℝ) * Real.log k
        - (Real.log k + Real.log ((k - 1 : ℕ) : ℝ)) / 2
        - Real.log (2 * Real.pi)
        - ((s + 1 : ℕ) : ℝ) ^ 2 / k := by
      linarith [hlogj]
    refine le_trans this ?_
    rw [hident]
    exact hleft
  linarith [hstep1, hstep2, hstep3, hsimp, hfinal]

lemma log_nat_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b : ℝ) = Real.log a + Real.log b :=
  Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')

/-- Real form of the mid-cut monomial. -/
lemma mid_cut_monomial_log (k : ℕ) (hk : 81 ≤ k)
    (s j : ℕ) (hs : s = midShift k) (hj : j = k - s) :
    Real.log ((2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
      ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k) =
    Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
      + (2 * s + 1 : ℝ) * Real.log ((j - 1 : ℕ) : ℝ)
      + 2 * Real.log k := by
  have hb := mid_cut_bounds k hk
  have hj0 : (0 : ℝ) < j := by
    have : 24 ≤ j := by rw [hj, hs]; exact hb.1
    exact_mod_cast (show 0 < j by omega)
  have hf0 : (0 : ℝ) < (j - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hbase : (0 : ℝ) < (j - 1 : ℕ) := by
    have : 24 ≤ j := by rw [hj, hs]; exact hb.1
    exact_mod_cast (show 0 < j - 1 by omega)
  have hp0 : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) := pow_pos hbase _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
  push_cast
  ring

lemma mid_cut_term_le (k : ℕ) (hk : 81 ≤ k) :
    let s := midShift k
    let j := k - s
    2 * j * (j - 1).factorial * (j - 1).factorial *
      (j - 1) ^ (2 * s + 1) * k * k
        ≤ k.factorial * (k - 1).factorial := by
  intro s j
  have hb := mid_cut_bounds k hk
  have hj24 : 24 ≤ j := by simpa [j, s] using hb.1
  have hcast :
      ((2 * j * (j - 1).factorial * (j - 1).factorial *
        (j - 1) ^ (2 * s + 1) * k * k : ℕ) : ℝ) =
      (2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
        ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k := by norm_cast
  have hcastR :
      ((k.factorial * (k - 1).factorial : ℕ) : ℝ) =
      (k.factorial : ℝ) * ((k - 1).factorial : ℝ) := by norm_cast
  have hposL : (0 : ℝ) <
      (2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
        ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hf0 : (0 : ℝ) < (j - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hbse : (0 : ℝ) < (j - 1 : ℕ) := by exact_mod_cast (show 0 < j - 1 by omega)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hposR : (0 : ℝ) < (k.factorial : ℝ) * ((k - 1).factorial : ℝ) := by
    have : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have : (0 : ℝ) < (k - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hlog := mid_cut_log_diff_le k hk
  have hexp := mid_cut_monomial_log k hk s j rfl rfl
  have hpow : (2 * s + 1 : ℝ) = (2 * k - 2 * j + 1 : ℝ) := by
    have hnat : (2 * s + 1 : ℕ) = 2 * k - 2 * j + 1 := by
      have := hb.2.2.2
      omega
    have hle : 2 * j ≤ 2 * k := by omega
    calc
      (2 * s + 1 : ℝ) = ((2 * s + 1 : ℕ) : ℝ) := by norm_cast
      _ = ((2 * k - 2 * j + 1 : ℕ) : ℝ) := by rw [hnat]
      _ = (2 * k - 2 * j + 1 : ℝ) := by
          rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
          simp [Nat.cast_mul]
  have hjm : (j - 1 : ℝ) = ((j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  have hineq :
      Real.log ((2 : ℝ) * j * (j - 1).factorial * (j - 1).factorial *
        ((j - 1 : ℕ) : ℝ) ^ (2 * s + 1) * k * k)
      ≤ Real.log ((k.factorial : ℝ) * ((k - 1).factorial : ℝ)) := by
    rw [hexp, log_nat_mul (Nat.factorial_pos _) (Nat.factorial_pos _)]
    -- hlog after unfolding lets
    have : Real.log 2 + Real.log j + 2 * Real.log ((j - 1).factorial : ℝ)
        + (2 * k - 2 * j + 1 : ℝ) * Real.log (j - 1 : ℝ)
        - Real.log (k.factorial : ℝ) - Real.log ((k - 1).factorial : ℝ)
        + 2 * Real.log k ≤ 0 := hlog
    rw [hpow, ← hjm]
    linarith
  have := (Real.log_le_log_iff hposL hposR).1 hineq
  have : ((2 * j * (j - 1).factorial * (j - 1).factorial *
      (j - 1) ^ (2 * s + 1) * k * k : ℕ) : ℝ)
      ≤ ((k.factorial * (k - 1).factorial : ℕ) : ℝ) := by
    rwa [hcast, hcastR]
  exact Nat.cast_le.mp this
