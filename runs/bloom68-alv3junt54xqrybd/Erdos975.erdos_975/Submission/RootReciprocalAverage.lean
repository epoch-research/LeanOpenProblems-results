import Submission.SmallDivisorAverage

/-!
# Root-reciprocal averages from linear root-count averages

A finite Abel summation identity and weighted harmonic Cesàro convergence show
that `rootCountSummatory g N / N → κ` implies
`rootReciprocalSum g N / log N → κ`. For a positive sequence whose divisibility
predicates depend only on residues, this also gives the normalized `smallAlong`
limit, with no separate root-reciprocal hypothesis.

These are supporting results for arbitrary sequences, not a polynomial
divisor-average conjecture. No sign assumption on `κ` is needed.
-/

namespace Erdos975Support

open Filter Asymptotics
open scoped Topology

/-- Weighted harmonic Cesàro convergence, normalized by the natural logarithm.
The weight of the `k`th term is `1 / (k + 1)`. -/
theorem weighted_harmonic_limit_of_tendsto {u : ℕ → ℝ} {κ : ℝ}
    (hu : Tendsto u atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦
      (∑ k ∈ Finset.range N, u k / ((k : ℝ) + 1)) / Real.log (N : ℝ))
      atTop (𝓝 κ) := by
  let w : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hsum (N : ℕ) : (∑ k ∈ Finset.range N, w k) = (harmonic N : ℝ) := by
    simp [w, harmonic, one_div]
  have hlower (N : ℕ) : Real.log (N : ℝ) ≤ (harmonic N : ℝ) := by
    simpa only [Nat.floor_natCast] using
      log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
  have hdiverge : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, w k) atTop atTop := by
    have hh : Tendsto (fun N : ℕ ↦ (harmonic N : ℝ)) atTop atTop :=
      tendsto_atTop_mono hlower tendsto_log_nat_atTop
    exact hh.congr fun N ↦ (hsum N).symm
  have hsmall : (fun k ↦ (u k - κ) * w k) =o[atTop] w := by
    have hzero : Tendsto (fun k ↦ u k - κ) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hu
    simpa only [one_mul] using
      ((isLittleO_one_iff ℝ).mpr hzero).mul_isBigO (isBigO_refl w atTop)
  have herr : Tendsto (fun N : ℕ ↦
      (∑ k ∈ Finset.range N, (u k - κ) * w k) / (harmonic N : ℝ))
      atTop (𝓝 0) := by
    have ht :=
      (hsmall.sum_range (fun k ↦ by dsimp [w]; positivity) hdiverge).tendsto_div_nhds_zero
    exact ht.congr fun N ↦ by rw [hsum]
  have ht := (herr.mul tendsto_harmonic_div_log_nat).add
    (tendsto_harmonic_div_log_nat.const_mul κ)
  simp only [mul_one, zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hh : (harmonic N : ℝ) ≠ 0 :=
    ne_of_gt ((Real.log_pos hN1).trans_le (hlower N))
  rw [div_mul_div_cancel₀ hh, ← mul_div_assoc, ← add_div]
  congr 1
  rw [← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [w]
  ring

/-- Finite Abel summation for the residue root counts. The interval is exactly
`1 ≤ k < N`; the formula is also valid at `N = 0`. -/
theorem rootReciprocalSum_eq_abel (g : ℕ → ℕ) (N : ℕ) :
    rootReciprocalSum g N = rootCountSummatory g N / (N : ℝ) +
      ∑ k ∈ Finset.Ico 1 N,
        (rootCountSummatory g k / (k : ℝ)) / ((k : ℝ) + 1) := by
  induction N with
  | zero => simp [rootReciprocalSum, rootCountSummatory]
  | succ N ih =>
    have hP : rootCountSummatory g (N + 1) =
        rootCountSummatory g N + (rootCount g (N + 1) : ℝ) := by
      unfold rootCountSummatory
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    have hH : rootReciprocalSum g (N + 1) =
        rootReciprocalSum g N + (rootCount g (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      unfold rootReciprocalSum
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    by_cases hN : N = 0
    · subst N
      simp [rootReciprocalSum, rootCountSummatory]
    · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
      rw [hH, ih, hP, Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hN)]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- A linear root-count average determines the logarithmic root-reciprocal
average. Neither positivity of `g` nor a sign assumption on `κ` is required. -/
theorem tendsto_rootReciprocalSum_of_rootCountSummatory {g : ℕ → ℕ} {κ : ℝ}
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ rootReciprocalSum g N / Real.log (N : ℝ))
      atTop (𝓝 κ) := by
  have hweighted := weighted_harmonic_limit_of_tendsto hP
  have hboundary : Tendsto (fun N : ℕ ↦
      (rootCountSummatory g N / (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 0) := hP.div_atTop tendsto_log_nat_atTop
  have ht := hboundary.add hweighted
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← add_div, rootReciprocalSum_eq_abel]
  congr 2
  rw [Finset.sum_range_eq_add_Ico _ (show 0 < N by omega)]
  simp [rootCountSummatory]

/-- For a positive residue-invariant sequence, the linear root-count limit
alone implies the normalized small-divisor limit. -/
theorem tendsto_smallAlong_of_linear_rootCount {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ smallAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ) :=
  tendsto_smallAlong_of_root_limits hg hmod
    (tendsto_rootReciprocalSum_of_rootCountSummatory hP) hP

end Erdos975Support
