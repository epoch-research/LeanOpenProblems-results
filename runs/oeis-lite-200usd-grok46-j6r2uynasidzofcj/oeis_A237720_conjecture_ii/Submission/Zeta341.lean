import FormalConjectures.Util.ProblemImports

open Complex Real
open scoped ArithmeticFunction
open ArithmeticFunction hiding log
open Chebyshev

noncomputable section

lemma trig_341 (phi : ℝ) : 0 ≤ 3 + 4 * Real.cos phi + Real.cos (2 * phi) := by
  have h2 : Real.cos (2 * phi) = 2 * Real.cos phi ^ 2 - 1 := Real.cos_two_mul phi
  have h : 3 + 4 * Real.cos phi + Real.cos (2 * phi) = 2 * (1 + Real.cos phi) ^ 2 := by
    rw [h2]; ring
  rw [h]
  nlinarith [sq_nonneg (1 + Real.cos phi)]

lemma vonMangoldt_zero' : vonMangoldt 0 = 0 := by
  rw [vonMangoldt_apply]
  simp [not_isPrimePow_zero]

lemma re_nat_cpow_neg {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ((n : ℂ) ^ (-s)).re =
      (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← ofReal_natCast n, ofReal_log (Nat.cast_nonneg n)]
  -- n^{-s} = exp(log n * (-s))
  rw [cpow_def_of_ne_zero hn0]
  -- Re(exp w) = exp(Re w) * cos(Im w)
  rw [Complex.exp_re]
  -- substitute log
  rw [hlog]
  -- Re(r * (-s)) = r * (-s.re), Im = r * (-s.im) for real r
  have hre : ((Real.log n : ℂ) * (-s)).re = Real.log n * -s.re := by
    rw [mul_re, ofReal_re, ofReal_im, neg_re, neg_im]
    ring
  have him : ((Real.log n : ℂ) * (-s)).im = Real.log n * -s.im := by
    rw [mul_im, ofReal_re, ofReal_im, neg_re, neg_im]
    ring
  rw [hre, him]
  have hexp : Real.exp (Real.log n * -s.re) = (n : ℝ) ^ (-s.re) := by
    rw [Real.exp_mul, Real.exp_log hnpos]
  rw [hexp]
  congr 1
  -- cos(log n * (-s.im)) = cos(s.im * log n)
  rw [show Real.log n * -s.im = -(s.im * Real.log n) by ring, Real.cos_neg]

lemma re_term_vonMangoldt (n : ℕ) (s : ℂ) :
    (LSeries.term (fun k => (vonMangoldt k : ℂ)) s n).re =
      if n = 0 then 0
      else vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term_zero]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [if_neg hn, LSeries.term_def₀ (by exact_mod_cast vonMangoldt_zero')]
    rw [mul_re, ofReal_re, ofReal_im, re_nat_cpow_neg hpos]
    simp
    ring

lemma summable_re_term_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => (LSeries.term (fun k => (vonMangoldt k : ℂ)) s n).re :=
  (LSeriesSummable_vonMangoldt hs).map Complex.reCLM Complex.continuous_re

lemma re_LSeries_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) s).re =
      ∑' n : ℕ, (LSeries.term (fun k => (vonMangoldt k : ℂ)) s n).re :=
  re_tsum (LSeriesSummable_vonMangoldt hs)

/-- Combined 3-4-1 coefficient at a single `n`. -/
def coeff341 (σ t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else vonMangoldt n * (n : ℝ) ^ (-σ) *
    (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n))

lemma coeff341_nonneg (σ t : ℝ) (n : ℕ) : 0 ≤ coeff341 σ t n := by
  simp only [coeff341]
  split_ifs
  · exact le_rfl
  · have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
    have hpow : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have htrig : 0 ≤ 3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n) := by
      convert trig_341 (t * Real.log n) using 2
      ring
    exact mul_nonneg (mul_nonneg hΛ hpow) htrig

lemma term_combo_eq_coeff341 (σ t : ℝ) (n : ℕ) :
    3 * (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n).re +
    4 * (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ + I * t) n).re +
    (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ + 2 * I * t) n).re =
      coeff341 σ t n := by
  rw [re_term_vonMangoldt, re_term_vonMangoldt, re_term_vonMangoldt]
  simp only [coeff341, ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im]
  split_ifs with hn
  · simp
  · simp
    ring

/-- The 3-4-1 positivity for `L ↗Λ`. -/
lemma re_logDeriv_341 {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)).re +
        4 * (LSeries (fun n => (vonMangoldt n : ℂ)) (σ + I * t)).re +
        (LSeries (fun n => (vonMangoldt n : ℂ)) (σ + 2 * I * t)).re := by
  have hs0 : 1 < (σ : ℂ).re := by simp [hσ]
  have hs1 : 1 < (σ + I * t : ℂ).re := by simp [hσ]
  have hs2 : 1 < (σ + 2 * I * t : ℂ).re := by simp [hσ]
  rw [re_LSeries_vonMangoldt hs0, re_LSeries_vonMangoldt hs1, re_LSeries_vonMangoldt hs2]
  have h0 := summable_re_term_vonMangoldt hs0
  have h1 := summable_re_term_vonMangoldt hs1
  have h2 := summable_re_term_vonMangoldt hs2
  rw [← tsum_mul_left, ← tsum_mul_left]
  have h3a : Summable fun n =>
      3 * (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n).re := h0.mul_left 3
  have h4b : Summable fun n =>
      4 * (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ + I * t) n).re := h1.mul_left 4
  rw [← h3a.tsum_add h4b, ← (h3a.add h4b).tsum_add h2]
  refine tsum_nonneg fun n => ?_
  have heq := term_combo_eq_coeff341 σ t n
  have hnn := coeff341_nonneg σ t n
  linarith

/-! ## Bound on `L Λ(σ)` for real `σ > 1` -/

lemma two_rpow_one_sub {σ : ℝ} (hσ : 1 < σ) : (2 : ℝ) ^ (1 - σ) < 1 := by
  have h : (1 : ℝ) - σ < 0 := by linarith
  have : (2 : ℝ) ^ (1 - σ) < (2 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
  simpa using this

lemma geom_sum_rpow {σ : ℝ} (hσ : 1 < σ) :
    ∑' k : ℕ, (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) = (1 - (2 : ℝ) ^ (1 - σ))⁻¹ := by
  have hr : ‖(2 : ℝ) ^ (1 - σ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact two_rpow_one_sub hσ
  have hgeom := tsum_geometric_of_norm_lt_one (ξ := (2 : ℝ) ^ (1 - σ)) hr
  convert hgeom using 1
  refine tsum_congr fun k => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

lemma psi_le_C (x : ℝ) (hx : 0 ≤ x) : ψ x ≤ (Real.log 4 + 4) * x :=
  psi_le_const_mul_self hx

lemma one_sub_two_rpow_ge {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (σ - 1) * Real.log 2 / 4 ≤ 1 - (2 : ℝ) ^ (1 - σ) := by
  set u := (σ - 1) * Real.log 2
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
  have hu1 : u ≤ Real.log 2 := by
    have : σ - 1 ≤ 1 := by linarith
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h2 : (2 : ℝ) ^ (1 - σ) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    simp [u]
    ring
  rw [h2]
  have habs : |(-u)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hu0]
    exact le_trans hu1 (le_of_lt (by
      have : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr this))
  have hexp : Real.exp (-u) ≤ 1 - u + u ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le habs
    rw [abs_le] at h
    linarith
  -- 1 - exp(-u) ≥ u - u² = u(1-u) ≥ u(1-log 2) > u/4
  have hlog2 : Real.log 2 < (3 / 4 : ℝ) :=
    lt_trans log_two_lt_d9 (by norm_num)
  nlinarith [sq_nonneg u]

lemma re_LSeries_eq_sum_vonMangoldt {σ : ℝ} (hσ : 1 < σ) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)).re =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else vonMangoldt n * (n : ℝ) ^ (-σ) := by
  have hs : 1 < (σ : ℂ).re := by simp [hσ]
  rw [re_LSeries_vonMangoldt hs]
  refine tsum_congr fun n => ?_
  rw [re_term_vonMangoldt]
  split_ifs
  · rfl
  · simp

lemma log_four_lt_two : Real.log 4 < 2 := by
  have h : (4 : ℝ) < Real.exp 2 := by
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; ring
    nlinarith [Real.exp_pos 1]
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h

lemma dyadic_block_bound (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ),
        vonMangoldt n * (n : ℝ) ^ (-σ) ≤
      2 * (Real.log 4 + 4) * (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) := by
  set lo : ℕ := 2 ^ k + 1
  set hi : ℕ := 2 ^ (k + 1)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpow : ∀ n ∈ Finset.Icc lo hi,
      (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(k : ℝ) * σ) := by
    intro n hn
    simp only [Finset.mem_Icc, lo, hi] at hn
    have hnpos : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 1)
        (le_trans (Nat.succ_le_succ (Nat.zero_le _)) hn.1))
    have h2k : (2 : ℝ) ^ (k : ℕ) ≤ (n : ℝ) := by
      have : (2 : ℕ) ^ k ≤ n := (Nat.le_succ _).trans hn.1
      exact_mod_cast this
    have hbase : (0 : ℝ) < (2 : ℝ) ^ (k : ℕ) :=
      pow_pos h2pos _
    have : (n : ℝ) ^ (-σ) ≤ ((2 : ℝ) ^ (k : ℕ)) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hbase h2k (by linarith)
    have heq : ((2 : ℝ) ^ (k : ℕ)) ^ (-σ) = (2 : ℝ) ^ (-(k : ℝ) * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h2pos)]
      ring_nf
    linarith
  have hsumΛ :
      ∑ n ∈ Finset.Icc lo hi, vonMangoldt n ≤ ψ (hi : ℝ) := by
    have hψ : ψ (hi : ℝ) = ∑ d ∈ Finset.Icc 0 hi, vonMangoldt d := by
      rw [psi_eq_sum_Icc, Nat.floor_natCast]
    rw [hψ]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => vonMangoldt_nonneg)
    intro n hn
    simp only [Finset.mem_Icc, lo] at hn ⊢
    exact ⟨Nat.zero_le n, hn.2⟩
  have hψC : ψ (hi : ℝ) ≤ (Real.log 4 + 4) * (hi : ℝ) :=
    psi_le_C (hi : ℝ) (Nat.cast_nonneg _)
  have hrpow_nn : 0 ≤ (2 : ℝ) ^ (-(k : ℝ) * σ) :=
    Real.rpow_nonneg (le_of_lt h2pos) _
  have h2 : (hi : ℝ) = 2 * (2 : ℝ) ^ (k : ℝ) := by
    simp only [hi, pow_succ', Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hcombine : (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-(k : ℝ) * σ) =
      (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) := by
    rw [← Real.rpow_add h2pos]
    ring_nf
  calc
    ∑ n ∈ Finset.Icc lo hi, vonMangoldt n * (n : ℝ) ^ (-σ)
        ≤ ∑ n ∈ Finset.Icc lo hi,
            vonMangoldt n * (2 : ℝ) ^ (-(k : ℝ) * σ) := by
      refine Finset.sum_le_sum fun n hn => ?_
      exact mul_le_mul_of_nonneg_left (hpow n hn) vonMangoldt_nonneg
    _ = (∑ n ∈ Finset.Icc lo hi, vonMangoldt n) *
          (2 : ℝ) ^ (-(k : ℝ) * σ) := by
      rw [Finset.sum_mul]
    _ ≤ (Real.log 4 + 4) * (hi : ℝ) * (2 : ℝ) ^ (-(k : ℝ) * σ) := by
      exact mul_le_mul_of_nonneg_right (le_trans hsumΛ hψC) hrpow_nn
    _ = (Real.log 4 + 4) * (2 * (2 : ℝ) ^ (k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) * σ) := by
      rw [h2]
    _ = 2 * (Real.log 4 + 4) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (-(k : ℝ) * σ)) := by
      ring
    _ = 2 * (Real.log 4 + 4) * (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) := by
      rw [hcombine]

/-- The summand `Λ(n) n^{-σ}` (with the n=0 convention). -/
def vmRpow (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else vonMangoldt n * (n : ℝ) ^ (-σ)

lemma vmRpow_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ vmRpow σ n := by
  unfold vmRpow; split_ifs
  · exact le_rfl
  · exact mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma vmRpow_eq (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    vmRpow σ n = vonMangoldt n * (n : ℝ) ^ (-σ) := by
  simp [vmRpow, hn]

lemma vmRpow_block_eq (σ : ℝ) (k : ℕ) :
    ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ), vmRpow σ n =
      ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ),
        vonMangoldt n * (n : ℝ) ^ (-σ) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    simp only [Finset.mem_Icc] at hn; omega
  exact vmRpow_eq σ hn0

/-- Every `n` with `2 ≤ n < N` lies in some dyadic block `Icc (2^k+1) (2^{k+1})` for `k < N`. -/
lemma mem_some_dyadic_block {n N : ℕ} (h2 : 2 ≤ n) (hn : n < N) :
    ∃ k < N, n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) h2
  set k := Nat.log2 n
  have hk_le : 2 ^ k ≤ n := Nat.log2_self_le hn0.ne'
  have hk_lt : n < 2 ^ (k + 1) := Nat.lt_log2_self
  have hk_ltN : k < N :=
    lt_of_le_of_lt (Nat.log2_le_self n) hn
  by_cases heq : n = 2 ^ k
  · have hkpos : 0 < k := by
      have : 1 < 2 ^ k := heq ▸ (lt_of_lt_of_le (by decide : 1 < 2) h2)
      exact Nat.pos_of_ne_zero fun hk0 => by simp [hk0] at this
    refine ⟨k - 1, lt_of_lt_of_le (Nat.sub_one_lt hkpos.ne') (Nat.le_of_lt hk_ltN), ?_⟩
    simp only [Finset.mem_Icc]
    have hpow : 2 ^ (k - 1 + 1) = 2 ^ k := by rw [Nat.sub_add_cancel hkpos]
    refine ⟨?_, ?_⟩
    · have : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
        rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hkpos]
      omega
    · rw [hpow, ← heq]
  · refine ⟨k, hk_ltN, ?_⟩
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_le_iff.mpr (lt_of_le_of_ne hk_le (Ne.symm heq)), Nat.le_of_lt hk_lt⟩

lemma vmRpow_zero (σ : ℝ) : vmRpow σ 0 = 0 := by simp [vmRpow]
lemma vmRpow_one (σ : ℝ) : vmRpow σ 1 = 0 := by simp [vmRpow, vonMangoldt_apply_one]

lemma sum_vmRpow_range_le_blocks {σ : ℝ} (N : ℕ) :
    ∑ n ∈ Finset.range N, vmRpow σ n ≤
      ∑ k ∈ Finset.range N,
        ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ), vmRpow σ n := by
  have hnn : ∀ n, 0 ≤ vmRpow σ n := vmRpow_nonneg σ
  -- For each `n < N`, `vmRpow n` is dominated by the sum of its copies over blocks containing `n`.
  have hterm : ∀ n ∈ Finset.range N,
      vmRpow σ n ≤
        ∑ k ∈ Finset.range N,
          (if n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ) then vmRpow σ n else (0 : ℝ)) := by
    intro n hn
    simp only [Finset.mem_range] at hn
    rcases lt_trichotomy n 2 with hn2 | rfl | hn2
    · -- n = 0 or 1
      interval_cases n
      · simp [vmRpow_zero]
      · simp [vmRpow_one]
    · -- n = 2: belongs to block k = 0
      have hmem : (2 : ℕ) ∈ Finset.Icc (2 ^ 0 + 1 : ℕ) (2 ^ (0 + 1) : ℕ) := by
        simp
      have h0 : 0 ∈ Finset.range N := Finset.mem_range.mpr (lt_of_le_of_lt (by decide : 0 ≤ 2) hn)
      refine le_trans ?_ (Finset.single_le_sum (fun k _ => by split_ifs <;> simp [hnn]) h0)
      · simp
    · -- n ≥ 2, n ≠ 2 so 2 < n
      have h2le : 2 ≤ n := le_of_lt hn2
      obtain ⟨k, hkN, hkmem⟩ := mem_some_dyadic_block h2le hn
      have hk : k ∈ Finset.range N := Finset.mem_range.mpr hkN
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => by split_ifs <;> simp [hnn]) hk)
      · simp [hkmem]
  let ind (n k : ℕ) : ℝ :=
    if n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ) then vmRpow σ n else (0 : ℝ)
  have hswap : ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N, ind n k =
      ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range N, ind n k := Finset.sum_comm
  have hinner : ∀ k, ∑ n ∈ Finset.range N, ind n k ≤
      ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ), vmRpow σ n := by
    intro k
    have hite : ∑ n ∈ Finset.range N, ind n k =
        ∑ n ∈ Finset.range N ∩ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ), vmRpow σ n := by
      simp only [ind]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      rfl
    rw [hite]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => hnn _)
  calc
    ∑ n ∈ Finset.range N, vmRpow σ n
        ≤ ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N, ind n k := by
      refine Finset.sum_le_sum ?_
      intro n hn
      simpa [ind] using hterm n hn
    _ = ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range N, ind n k := hswap
    _ ≤ ∑ k ∈ Finset.range N,
          ∑ n ∈ Finset.Icc (2 ^ k + 1 : ℕ) (2 ^ (k + 1) : ℕ), vmRpow σ n :=
      Finset.sum_le_sum fun k _ => hinner k

/-- Partial sums of `vmRpow` are bounded by a constant independent of `N`. -/
lemma sum_vmRpow_range_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    ∑ n ∈ Finset.range N, vmRpow σ n ≤
      2 * (Real.log 4 + 4) * (1 - (2 : ℝ) ^ (1 - σ))⁻¹ := by
  have hblocks : ∑ n ∈ Finset.range N, vmRpow σ n ≤
      ∑ k ∈ Finset.range N, 2 * (Real.log 4 + 4) * (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) := by
    refine le_trans (sum_vmRpow_range_le_blocks N) ?_
    refine Finset.sum_le_sum fun k hk => ?_
    rw [vmRpow_block_eq]
    exact dyadic_block_bound k hσ
  have hC : 0 ≤ 2 * (Real.log 4 + 4) := by
    have : 0 ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
    linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (1 - σ) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr1 : (2 : ℝ) ^ (1 - σ) < 1 := two_rpow_one_sub hσ
  have hgeom : ∑ k ∈ Finset.range N, (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) ≤
      (1 - (2 : ℝ) ^ (1 - σ))⁻¹ := by
    have hterm : ∀ k : ℕ, (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) = ((2 : ℝ) ^ (1 - σ)) ^ k := by
      intro k
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    have hico := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hr0 hr1
    rw [Finset.range_eq_Ico]
    refine le_trans hico ?_
    rw [pow_zero, one_div]
  calc
    ∑ n ∈ Finset.range N, vmRpow σ n
        ≤ ∑ k ∈ Finset.range N,
            2 * (Real.log 4 + 4) * (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) := hblocks
    _ = 2 * (Real.log 4 + 4) * ∑ k ∈ Finset.range N, (2 : ℝ) ^ ((k : ℝ) * (1 - σ)) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log 4 + 4) * (1 - (2 : ℝ) ^ (1 - σ))⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom hC

lemma C_mul_inv_one_sub_two_rpow_le {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    2 * (Real.log 4 + 4) * (1 - (2 : ℝ) ^ (1 - σ))⁻¹ ≤ 80 / (σ - 1) := by
  have hσpos : 0 < σ - 1 := sub_pos.mpr hσ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden := one_sub_two_rpow_ge hσ hσ2
  have hdenpos : 0 < 1 - (2 : ℝ) ^ (1 - σ) := sub_pos.mpr (two_rpow_one_sub hσ)
  have hC : Real.log 4 + 4 < 6 := by linarith [log_four_lt_two]
  have hnum' : 0 < (σ - 1) * Real.log 2 := mul_pos hσpos hlog2pos
  have hquarterpos : 0 < (σ - 1) * Real.log 2 / 4 := div_pos hnum' (by norm_num)
  have h1 : (1 - (2 : ℝ) ^ (1 - σ))⁻¹ ≤ 4 / ((σ - 1) * Real.log 2) := by
    have := inv_anti₀ hquarterpos hden
    -- `inv ((σ-1)log 2 / 4) = 4 / ((σ-1)log 2)`
    have hinv : ((σ - 1) * Real.log 2 / 4)⁻¹ = 4 / ((σ - 1) * Real.log 2) := by
      field
    rwa [hinv] at this
  have hC' : 0 ≤ 2 * (Real.log 4 + 4) := by
    have : 0 ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
    linarith
  have hmul : 2 * (Real.log 4 + 4) * (1 - (2 : ℝ) ^ (1 - σ))⁻¹ ≤
      2 * 6 * (4 / ((σ - 1) * Real.log 2)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hC.le (by norm_num)) h1 ?_ ?_
    · exact inv_nonneg.mpr (le_of_lt hdenpos)
    · linarith
  have h48 : (48 : ℝ) / ((σ - 1) * Real.log 2) ≤ 80 / (σ - 1) := by
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := log_two_gt_d9
    rw [div_le_div_iff₀ (mul_pos hσpos hlog2pos) hσpos]
    nlinarith [hlog2]
  have heq : (2 : ℝ) * 6 * (4 / ((σ - 1) * Real.log 2)) = 48 / ((σ - 1) * Real.log 2) := by ring
  linarith

lemma summable_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => if n = 0 then (0 : ℝ) else vonMangoldt n * (n : ℝ) ^ (-σ) := by
  have hs : 1 < (σ : ℂ).re := by simp [hσ]
  refine (summable_re_term_vonMangoldt hs).congr fun n => ?_
  rw [re_term_vonMangoldt]
  split_ifs <;> simp

lemma vmRpow_eq_ite (σ : ℝ) (n : ℕ) :
    vmRpow σ n = (if n = 0 then (0 : ℝ) else vonMangoldt n * (n : ℝ) ^ (-σ)) := rfl

/-- `Σ Λ(n) n^{-σ} ≤ 80 / (σ - 1)` for `1 < σ ≤ 2`. -/
lemma LSeries_vonMangoldt_real_bound_of_le_two {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)).re ≤ 80 / (σ - 1) := by
  rw [re_LSeries_eq_sum_vonMangoldt hσ]
  have htsum : ∑' n : ℕ, vmRpow σ n ≤
      2 * (Real.log 4 + 4) * (1 - (2 : ℝ) ^ (1 - σ))⁻¹ :=
    Real.tsum_le_of_sum_range_le (vmRpow_nonneg σ) (sum_vmRpow_range_le hσ)
  have heq : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else vonMangoldt n * (n : ℝ) ^ (-σ)) =
      ∑' n : ℕ, vmRpow σ n :=
    tsum_congr fun n => (vmRpow_eq_ite σ n).symm
  rw [heq]
  exact le_trans htsum (C_mul_inv_one_sub_two_rpow_le hσ hσ2)

/-- `Σ Λ(n) n^{-σ} ≤ 80 / (σ - 1)` for `1 < σ ≤ 2`.
This is the range needed for the classical zero-free region. -/
lemma LSeries_vonMangoldt_real_bound {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ)).re ≤ 80 / (σ - 1) :=
  LSeries_vonMangoldt_real_bound_of_le_two hσ hσ2
