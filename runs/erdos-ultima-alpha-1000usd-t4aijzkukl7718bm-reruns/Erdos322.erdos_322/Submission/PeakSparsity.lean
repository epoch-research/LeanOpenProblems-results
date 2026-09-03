import Submission.Spec

/-!
# Sparsity of unrestricted power-sized peaks

The elementary linear summatory bound implies convergence of weighted counting
series. Consequently every positive-power peak set has a convergent harmonic
series. This does not imply that such a set is finite and does not settle the
conjecture.
-/

namespace Erdos322Research.PeakSparsity

open Erdos322 Finset Filter
open scoped Topology
noncomputable section
set_option Elab.async false

private abbrev Rep (k n : ℕ) :=
  {a : Fin k → Fin (n+1) // ∑ i, (a i : ℕ)^k = n}

private theorem rep_card (k n : ℕ) :
    Fintype.card (Rep k n) = representationCount k n := by
  simp [Rep, Fintype.card_subtype, representationCount]

private def rootBoxMap (k N : ℕ) (hk : k ≠ 0)
    (v : (n : Fin (N+1)) × Rep k n) : Fin k → Fin (k.nthRoot N+1) :=
  fun i => ⟨v.2.1 i, by
    have hi : (v.2.1 i : ℕ)^k ≤ v.1 :=
      (Finset.single_le_sum (f := fun j : Fin k => (v.2.1 j : ℕ)^k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq v.2.2
    have hn : (v.1 : ℕ) ≤ N := Nat.le_of_lt_succ v.1.isLt
    exact Nat.lt_succ_of_le ((Nat.le_nthRoot_iff hk).mpr (hi.trans hn))⟩

private theorem rootBoxMap_injective (k N : ℕ) (hk : k ≠ 0) :
    Function.Injective (rootBoxMap k N hk) := by
  rintro ⟨n,a⟩ ⟨m,b⟩ he
  have hvals : ∀ i, (a.1 i : ℕ) = b.1 i := by
    intro i
    exact congrArg Fin.val (congrFun he i)
  have hnm : n = m := by
    apply Fin.ext
    calc
      (n : ℕ) = ∑ i, (a.1 i : ℕ)^k := a.2.symm
      _ = ∑ i, (b.1 i : ℕ)^k := by simp only [hvals]
      _ = m := b.2
  subst m
  congr 1
  apply Subtype.ext
  funext i
  exact Fin.ext (hvals i)

/-- The total number of representations up to `N` fits in the integer root box. -/
theorem summatory_count_le_root_box (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.range (N+1), representationCount k n ≤ (k.nthRoot N+1)^k := by
  classical
  have hc := Fintype.card_le_of_injective (rootBoxMap k N hk.ne')
    (rootBoxMap_injective k N hk.ne')
  simpa only [Fintype.card_sigma, rep_card, Fintype.card_fun, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range] using hc


/-- The full summatory count is bounded linearly, not just a restricted locus. -/
theorem summatory_count_linear (k N : ℕ) (hk : 0 < k) (hN : 1 ≤ N) :
    ∑ n ∈ range (N+1), (representationCount k n : ℝ) ≤ (2 : ℝ)^k * N := by
  have hroot : 1 ≤ k.nthRoot N := (Nat.le_nthRoot_iff hk.ne').mpr (by simpa using hN)
  have hbox : (k.nthRoot N+1)^k ≤ 2^k*N := by
    calc
      (k.nthRoot N+1)^k ≤ (2*k.nthRoot N)^k := Nat.pow_le_pow_left (by omega) k
      _ = 2^k*(k.nthRoot N)^k := Nat.mul_pow _ _ _
      _ ≤ 2^k*N := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (.inl hk.ne'))
  exact_mod_cast (summatory_count_le_root_box k N hk).trans hbox

/-- A linear summatory estimate for a nonnegative sequence gives convergence
of every weighted series with exponent strictly bigger than one. -/
theorem summable_weighted_of_summatory_linear (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ range (N+1), a n ≤ C*N)
    (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ ↦ a n * (n : ℝ)^(-s)) := by
  let w : ℕ → ℝ := fun n ↦ a n * (n : ℝ)^(-s)
  let g : ℕ → ℝ := fun j ↦ 2*C*((2 : ℝ)^(1-s))^j
  have hw : ∀ n, 0 ≤ w n := fun n ↦ mul_nonneg (ha n) (Real.rpow_nonneg (by positivity) _)
  have hg : ∀ j, 0 ≤ g j := by intro j; dsimp [g]; positivity
  have hgs : Summable g := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1-s))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left (2*C)
  have hblock (j : ℕ) : ∑ n ∈ Ico (2^j) (2^(j+1)), w n ≤ g j := by
    have hpow : (0 : ℝ) < ((2^j : ℕ) : ℝ) := by positivity
    have hweight (n : ℕ) (hn : n ∈ Ico (2^j) (2^(j+1))) :
        (n : ℝ)^(-s) ≤ ((2^j : ℕ) : ℝ)^(-s) :=
      Real.rpow_le_rpow_of_nonpos hpow (by exact_mod_cast (mem_Ico.mp hn).1) (by linarith)
    have hsub : ∑ n ∈ Ico (2^j) (2^(j+1)), a n ≤
        ∑ n ∈ range (2^(j+1)+1), a n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_range.mpr (by have := (mem_Ico.mp hn).2; omega)
      · intro n _ _; exact ha n
    calc
      ∑ n ∈ Ico (2^j) (2^(j+1)), w n ≤
          ∑ n ∈ Ico (2^j) (2^(j+1)), a n * ((2^j : ℕ) : ℝ)^(-s) :=
        sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (hweight n hn) (ha n)
      _ = (∑ n ∈ Ico (2^j) (2^(j+1)), a n) * ((2^j : ℕ) : ℝ)^(-s) := (sum_mul ..).symm
      _ ≤ (C * (2^(j+1) : ℕ)) * ((2^j : ℕ) : ℝ)^(-s) :=
        mul_le_mul_of_nonneg_right
          (hsub.trans (hbound _ (Nat.one_le_two_pow))) (Real.rpow_nonneg (by positivity) _)
      _ = g j := by
        dsimp [g]
        push_cast
        rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), pow_succ]
        have he : (2 : ℝ)^(1-s) = 2 * (2 : ℝ)^(-s) := by
          rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
        rw [he, mul_pow]
        ring
  have hdyadic (j : ℕ) : ∑ n ∈ range (2^j), w n ≤ w 0 + ∑ i ∈ range j, g i := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← sum_range_add_sum_Ico w (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j ≤ j+1)),
        sum_range_succ]
      linarith [hblock j]
  apply summable_of_sum_range_le hw (c := w 0 + ∑' j, g j)
  intro N
  calc
    ∑ n ∈ range N, w n ≤ ∑ n ∈ range (2^N), w n :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.lt_two_pow_self.le)) (fun n _ _ ↦ hw n)
    _ ≤ w 0 + ∑ j ∈ range N, g j := hdyadic N
    _ ≤ w 0 + ∑' j, g j := add_le_add le_rfl (hgs.sum_le_tsum _ (fun j _ ↦ hg j))

/-- Weighted summability for the actual unrestricted representation count. -/
theorem weighted_count_summable (k : ℕ) (hk : 0 < k) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ ↦ (representationCount k n : ℝ) * (n : ℝ)^(-s)) :=
  summable_weighted_of_summatory_linear (fun n ↦ representationCount k n)
    (fun _ ↦ by positivity) (2^k) (by positivity)
    (fun N hN ↦ summatory_count_linear k N hk hN) s hs

/-- Every power peak set has convergence exponent at most `1-c`.
The exponent `s` may be any real number with `1 < c+s`. -/
theorem peak_rpow_summable (k : ℕ) (hk : 0 < k) (c s : ℝ) (hs : 1 < c+s) :
    Summable (fun n : {n : ℕ | (n : ℝ)^c < representationCount k n} ↦
      ((n : ℕ) : ℝ)^(-s)) := by
  classical
  change Summable ((fun n : ℕ ↦ (n : ℝ)^(-s)) ∘
    (Subtype.val : {n : ℕ | (n : ℝ)^c < representationCount k n} → ℕ))
  rw [summable_subtype_iff_indicator]
  apply (weighted_count_summable k hk (c+s) hs).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  by_cases hp : (n : ℝ)^c < representationCount k n
  · rw [Set.indicator_of_mem (s := {n : ℕ | (n : ℝ)^c < representationCount k n}) hp, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      (n : ℝ)^(-s) = (n : ℝ)^c * (n : ℝ)^(-(c+s)) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      _ ≤ (representationCount k n : ℝ) * (n : ℝ)^(-(c+s)) :=
        mul_le_mul_of_nonneg_right hp.le (Real.rpow_nonneg hnpos.le _)
  · rw [Set.indicator_of_notMem (s := {n : ℕ | (n : ℝ)^c < representationCount k n}) hp, norm_zero]
    positivity

/-- Positive-power peak sets have a convergent harmonic series, even when infinite. -/
theorem peak_harmonic_summable (k : ℕ) (hk : 0 < k) (c : ℝ) (hc : 0 < c) :
    Summable (fun n : {n : ℕ | (n : ℝ)^c < representationCount k n} ↦
      (1 : ℝ) / (n : ℕ)) := by
  simpa only [Real.rpow_neg_one, one_div] using
    peak_rpow_summable k hk c 1 (by linarith)

/-- A quantitative bound on the number of positive power peaks up to `N`.
This holds for every nonnegative `s` strictly above `1-c`. -/
theorem peak_card_bound (k : ℕ) (hk : 0 < k) (c s : ℝ)
    (hs : 0 ≤ s) (hcs : 1 < c+s) :
    ∃ C ≥ (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      (((Icc 1 N : Finset ℕ).filter (fun n : ℕ ↦ (n : ℝ)^c < representationCount k n)).card : ℝ) ≤
        C*(N : ℝ)^s := by
  classical
  let P : Set ℕ := {n : ℕ | (n : ℝ)^c < representationCount k n}
  let f : ℕ → ℝ := P.indicator (fun n ↦ (n : ℝ)^(-s))
  have hf : Summable f := summable_subtype_iff_indicator.mp
    (peak_rpow_summable k hk c s hcs)
  have hf0 : ∀ n, 0 ≤ f n := Set.indicator_nonneg (fun n _ ↦ Real.rpow_nonneg (by positivity) _) 
  refine ⟨∑' n, f n, tsum_nonneg hf0, ?_⟩
  intro N hN
  let S := (Icc 1 N : Finset ℕ).filter (fun n : ℕ ↦ (n : ℝ)^c < representationCount k n)
  have hterm (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ (N : ℝ)^s * f n := by
    obtain ⟨hn, hp⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnP : n ∈ P := hp
    dsimp only [f]
    rw [Set.indicator_of_mem hnP]
    calc
      (1 : ℝ) = (n : ℝ)^s * (n : ℝ)^(-s) := by
        rw [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero]
      _ ≤ (N : ℝ)^s * (n : ℝ)^(-s) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN) hs)
          (Real.rpow_nonneg hnpos.le _)
  calc
    (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (N : ℝ)^s * f n := sum_le_sum hterm
    _ = (N : ℝ)^s * ∑ n ∈ S, f n := (mul_sum ..).symm
    _ ≤ (N : ℝ)^s * ∑' n, f n := mul_le_mul_of_nonneg_left
      (hf.sum_le_tsum S (fun n _ ↦ hf0 n)) (Real.rpow_nonneg (by positivity) _)
    _ = (∑' n, f n) * (N : ℝ)^s := mul_comm _ _

/-- Every positive-power peak set has zero natural density. The interval starts
at one only to omit the irrelevant exceptional index zero. -/
theorem peak_density_zero (k : ℕ) (hk : 0 < k) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦
      (((Icc 1 N : Finset ℕ).filter (fun n : ℕ ↦ (n : ℝ)^c < representationCount k n)).card : ℝ) / N)
      atTop (𝓝 0) := by
  let s : ℝ := 1 - min c 1 / 2
  have hmpos : 0 < min c 1 := lt_min hc zero_lt_one
  have hm1 : min c 1 ≤ 1 := min_le_right _ _
  have hmc : min c 1 ≤ c := min_le_left _ _
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hcs : 1 < c+s := by dsimp [s]; linarith
  obtain ⟨C, hC, hb⟩ := peak_card_bound k hk c s hs hcs
  have ht : Tendsto (fun N : ℕ ↦ C*(N : ℝ)^(s-1)) atTop (𝓝 0) := by
    have he : s-1 = -(1-s) := by ring
    simpa only [he, mul_zero] using
      ((tendsto_rpow_neg_atTop (by linarith : 0 < 1-s)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc
      _ ≤ C*(N : ℝ)^s / N := div_le_div_of_nonneg_right (hb N hN) hNpos.le
      _ = C*(N : ℝ)^(s-1) := by rw [Real.rpow_sub hNpos s 1, Real.rpow_one]; ring

/-- This actual cubic example prevents confusing harmonic summability with
finiteness: its peak set is both infinite and harmonically summable. -/
theorem cubic_peaks_infinite_and_harmonic_summable :
    {n : ℕ | (n : ℝ)^(1/12 : ℝ) < representationCount 3 n}.Infinite ∧
      Summable (fun n : {n : ℕ | (n : ℝ)^(1/12 : ℝ) < representationCount 3 n} ↦
        (1 : ℝ)/(n : ℕ)) :=
  ⟨cubic_exponent_one_twelfth, peak_harmonic_summable 3 (by decide) (1/12) (by norm_num)⟩

end
end Erdos322Research.PeakSparsity
