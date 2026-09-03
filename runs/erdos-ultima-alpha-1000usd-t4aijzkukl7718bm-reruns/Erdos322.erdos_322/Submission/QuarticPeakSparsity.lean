import Submission.QuarticHuaMoment

/-! Unrestricted quartic peak-set estimates from Hua's second moment.
These sparsity and summability conclusions do not imply finiteness of the
peak sets and do not settle the conjecture. -/
namespace Erdos322Research.QuarticPeakSparsity
noncomputable section
open Erdos322 Erdos322.MomentReduction QuarticHuaMoment Finset Filter
open scoped Topology Classical
set_option Elab.async false
set_option maxHeartbeats 0

/-- A polynomial summatory estimate gives convergence of weighted series
above the summatory exponent. The zero index is harmless. -/
theorem summable_weighted_of_summatory_power (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, a n ≤ C * (N : ℝ) ^ α)
    (s : ℝ) (hs : α < s) :
    Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-s)) := by
  let w : ℕ → ℝ := fun n ↦ a n * (n : ℝ) ^ (-s)
  let g : ℕ → ℝ := fun j ↦ C * (2 : ℝ) ^ α * ((2 : ℝ) ^ (α - s)) ^ j
  have hw : ∀ n, 0 ≤ w n := fun n ↦ mul_nonneg (ha n) (Real.rpow_nonneg (by positivity) _)
  have hg : ∀ j, 0 ≤ g j := by intro j; dsimp [g]; positivity
  have hgs : Summable g := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (α - s))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left (C * 2 ^ α)
  have hblock (j : ℕ) : ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), w n ≤ g j := by
    have hpow : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
    have hweight (n : ℕ) (hn : n ∈ Ico (2 ^ j) (2 ^ (j + 1))) :
        (n : ℝ) ^ (-s) ≤ ((2 ^ j : ℕ) : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hpow (by exact_mod_cast (mem_Ico.mp hn).1) (by linarith)
    have hsub : ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), a n ≤
        ∑ n ∈ Icc 1 (2 ^ (j + 1)), a n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
        exact mem_Icc.mpr ⟨Nat.one_le_two_pow.trans hn1, hn2.le⟩
      · intro n _ _; exact ha n
    calc
      ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), w n ≤
          ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), a n * ((2 ^ j : ℕ) : ℝ) ^ (-s) :=
        sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (hweight n hn) (ha n)
      _ = (∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), a n) * ((2 ^ j : ℕ) : ℝ) ^ (-s) :=
        (sum_mul ..).symm
      _ ≤ (C * ((2 ^ (j + 1) : ℕ) : ℝ) ^ α) * ((2 ^ j : ℕ) : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right (hsub.trans (hbound _ Nat.one_le_two_pow))
          (Real.rpow_nonneg (by positivity) _)
      _ = g j := by
        dsimp [g]
        push_cast
        rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), pow_succ]
        have he : (2 : ℝ) ^ (α - s) = 2 ^ α * (2 : ℝ) ^ (-s) := by
          rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
        rw [he, mul_pow]
        ring
  have hdyadic (j : ℕ) : ∑ n ∈ range (2 ^ j), w n ≤ w 0 + ∑ i ∈ range j, g i := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← sum_range_add_sum_Ico w
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j ≤ j + 1)), sum_range_succ]
      linarith [hblock j]
  apply summable_of_sum_range_le hw (c := w 0 + ∑' j, g j)
  intro N
  calc
    ∑ n ∈ range N, w n ≤ ∑ n ∈ range (2 ^ N), w n :=
      sum_le_sum_of_subset_of_nonneg (range_mono Nat.lt_two_pow_self.le) (fun n _ _ ↦ hw n)
    _ ≤ w 0 + ∑ j ∈ range N, g j := hdyadic N
    _ ≤ w 0 + ∑' j, g j := add_le_add le_rfl (hgs.sum_le_tsum _ (fun j _ ↦ hg j))

/-- Weighted convergence for every moment supplied by the current Hua bound.
The convergence threshold grows with the moment order. -/
theorem quartic_weighted_moment_summable (q : ℕ) (s : ℝ)
    (hs : 5 / 4 + (q : ℝ) / 2 < s) :
    Summable (fun n : ℕ ↦ (representationCount 4 n : ℝ) ^ (q + 2) * (n : ℝ) ^ (-s)) := by
  let δ : ℝ := (s - (5 / 4 + (q : ℝ) / 2)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hbound⟩ := quartic_higher_moment_upper q δ hδ
  apply summable_weighted_of_summatory_power
    (fun n ↦ (representationCount 4 n : ℝ) ^ (q + 2)) (fun _ ↦ by positivity)
    C (5 / 4 + (q : ℝ) / 2 + δ) hC.le (by positivity)
    (fun N hN ↦ hbound N hN) s
  dsimp [δ]
  linarith

/-- In particular the square count is summable with any weight `n^(-s)`
for `s > 5/4`. -/
theorem quartic_weighted_square_summable (s : ℝ) (hs : 5 / 4 < s) :
    Summable (fun n : ℕ ↦ (representationCount 4 n : ℝ) ^ 2 * (n : ℝ) ^ (-s)) := by
  simpa using quartic_weighted_moment_summable 0 s (by simpa using hs)

/-- The weighted peak estimate supplied by any of the available Hua moments. -/
theorem quartic_peak_rpow_summable_of_moment (q : ℕ) (c s : ℝ)
    (hcs : 5 / 4 + (q : ℝ) / 2 < ((q : ℝ) + 2) * c + s) :
    Summable (fun n : {n : ℕ | (n : ℝ) ^ c < representationCount 4 n} ↦
      ((n : ℕ) : ℝ) ^ (-s)) := by
  classical
  change Summable ((fun n : ℕ ↦ (n : ℝ) ^ (-s)) ∘
    (Subtype.val : {n : ℕ | (n : ℝ) ^ c < representationCount 4 n} → ℕ))
  rw [summable_subtype_iff_indicator]
  apply (quartic_weighted_moment_summable q (((q : ℝ) + 2) * c + s) hcs).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  by_cases hp : (n : ℝ) ^ c < representationCount 4 n
  · rw [Set.indicator_of_mem (s := {n : ℕ | (n : ℝ) ^ c < representationCount 4 n}) hp,
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : (n : ℝ) ^ (((q : ℝ) + 2) * c) ≤ (representationCount 4 n : ℝ) ^ (q + 2) := by
      have he : ((q : ℝ) + 2) * c = c * ((q + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_mul_natCast hnr.le]
      exact pow_le_pow_left₀ (by positivity) hp.le (q + 2)
    calc
      (n : ℝ) ^ (-s) = (n : ℝ) ^ (((q : ℝ) + 2) * c) * (n : ℝ) ^ (-(((q : ℝ) + 2) * c + s)) := by
        rw [← Real.rpow_add hnr]
        congr 1
        ring
      _ ≤ (representationCount 4 n : ℝ) ^ (q + 2) * (n : ℝ) ^ (-(((q : ℝ) + 2) * c + s)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hnr.le _)
  · rw [Set.indicator_of_notMem (s := {n : ℕ | (n : ℝ) ^ c < representationCount 4 n}) hp,
      norm_zero]
    positivity

/-- Power peaks have convergence exponent at most `5/4-2c`.
This improves the first-moment estimate when `c>1/4`. -/
theorem quartic_peak_rpow_summable (c s : ℝ) (hcs : 5 / 4 < 2 * c + s) :
    Summable (fun n : {n : ℕ | (n : ℝ) ^ c < representationCount 4 n} ↦
      ((n : ℕ) : ℝ) ^ (-s)) := by
  simpa using quartic_peak_rpow_summable_of_moment 0 c s (by simpa using hcs)

/-- A weighted summable set has a corresponding cardinality bound. -/
lemma card_bound_of_rpow_summable (P : Set ℕ) (s : ℝ) (hs : 0 ≤ s)
    (h : Summable (fun n : P ↦ ((n : ℕ) : ℝ) ^ (-s))) :
    ∃ C ≥ (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      (((Icc 1 N : Finset ℕ).filter (fun n ↦ n ∈ P)).card : ℝ) ≤ C * (N : ℝ) ^ s := by
  classical
  let f : ℕ → ℝ := P.indicator (fun n ↦ (n : ℝ) ^ (-s))
  have hf : Summable f := summable_subtype_iff_indicator.mp h
  have hf0 : ∀ n, 0 ≤ f n := Set.indicator_nonneg (fun n _ ↦ Real.rpow_nonneg (by positivity) _)
  refine ⟨∑' n, f n, tsum_nonneg hf0, fun N hN ↦ ?_⟩
  let S := (Icc 1 N : Finset ℕ).filter (fun n ↦ n ∈ P)
  have hterm (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ (N : ℝ) ^ s * f n := by
    obtain ⟨hn, hp⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    dsimp only [f]
    rw [Set.indicator_of_mem hp]
    calc
      (1 : ℝ) = (n : ℝ) ^ s * (n : ℝ) ^ (-s) := by
        rw [← Real.rpow_add hnr, add_neg_cancel, Real.rpow_zero]
      _ ≤ (N : ℝ) ^ s * (n : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN) hs)
          (Real.rpow_nonneg hnr.le _)
  calc
    (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (N : ℝ) ^ s * f n := sum_le_sum hterm
    _ = (N : ℝ) ^ s * ∑ n ∈ S, f n := (mul_sum ..).symm
    _ ≤ (N : ℝ) ^ s * ∑' n, f n := mul_le_mul_of_nonneg_left
      (hf.sum_le_tsum S (fun n _ ↦ hf0 n)) (Real.rpow_nonneg (by positivity) _)
    _ = (∑' n, f n) * (N : ℝ) ^ s := mul_comm _ _

/-- An unrestricted quantitative bound on the quartic peak set. -/
theorem quartic_peak_card_bound (c s : ℝ) (hs : 0 ≤ s) (hcs : 5 / 4 < 2 * c + s) :
    ∃ C ≥ (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      (((Icc 1 N : Finset ℕ).filter
        (fun n : ℕ ↦ (n : ℝ) ^ c < representationCount 4 n)).card : ℝ) ≤ C * (N : ℝ) ^ s :=
  card_bound_of_rpow_summable _ s hs (quartic_peak_rpow_summable c s hcs)

/-- For `c≤1/2`, higher orders in this particular moment family do not
improve on the second-moment convergence threshold. -/
theorem hua_threshold_ge_second (q : ℕ) (c : ℝ) (hc : c ≤ 1 / 2) :
    5 / 4 - 2 * c ≤ 5 / 4 + (q : ℝ) / 2 - ((q : ℝ) + 2) * c := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  nlinarith

/-- The same thresholds remain strictly positive throughout that range;
none yields summability of the constant-one peak weight there. -/
theorem hua_threshold_ge_quarter (q : ℕ) (c : ℝ) (hc : c ≤ 1 / 2) :
    1 / 4 ≤ 5 / 4 + (q : ℝ) / 2 - ((q : ℝ) + 2) * c := by
  have h := hua_threshold_ge_second q c hc
  linarith

end
end Erdos322Research.QuarticPeakSparsity
