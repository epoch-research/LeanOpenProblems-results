import Submission.PrefixMomentExplore

/-!
# A strict lower gap for the counting coefficient of a hypothetical witness

This necessary condition is consistent with Erdős Problem 66 and does not settle it.
-/

namespace Erdos66PrefixGap
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Cumulative
  Erdos66WeightedLog Erdos66RawMoment Erdos66PrefixMoment
open scoped Topology

lemma full_moment_limit_filter {A : Set ℕ} {c : ℝ} {l : Filter ℕ} (hl : l ≤ atTop)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (hcount : Tendsto (fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)) l (𝓝 c))
    (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun n : ℕ ↦ fullMoment A n k / ((n : ℝ) * Real.log n))
      l (𝓝 (c / ((k : ℝ) + 1))) := by
  have hlow := (log_weighted_power_limit h k hk).mono_left hl
  have htail := (hcount.sub ((cumulative_sumRep_limit h).mono_left hl)).const_mul ((2 : ℝ) ^ k)
  simp only [sub_self, mul_zero] at htail
  have herr : Tendsto (fun n : ℕ ↦ (fullMoment A n k - lowMoment A n k) /
      ((n : ℝ) * Real.log n)) l (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ htail
    · filter_upwards [Filter.Eventually.filter_mono hl (eventually_ge_atTop 2)] with n hn
      exact div_nonneg (moment_tail_bounds A n k (by omega)).1
        (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _))
    · filter_upwards [Filter.Eventually.filter_mono hl (eventually_ge_atTop 2)] with n hn
      have hb := (moment_tail_bounds A n k (by omega)).2
      have hh := div_le_div_of_nonneg_right hb
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (log_nat_nonneg n))
      simpa only [mul_div_assoc, sub_div] using hh
  have hh := hlow.add herr
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [] with n
  dsimp only [lowMoment]
  ring

lemma pair_moment_limit_filter {A : Set ℕ} {c : ℝ} {l : Filter ℕ}
    (hl : l ≤ atTop) (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (hcount : Tendsto (fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)) l (𝓝 c))
    (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun n : ℕ ↦ pairMoment (cutoff A n) (fun a : ℕ ↦ (a : ℝ) / n) k)
      l (𝓝 (1 / ((k : ℝ) + 1))) := by
  have hh := (full_moment_limit_filter hl h hcount k hk).div hcount hc
  have hlim : Tendsto (fun n : ℕ ↦
      (fullMoment A n k / ((n : ℝ) * Real.log n)) /
        ((count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)))
      l (𝓝 (1 / ((k : ℝ) + 1))) := by
    convert hh using 1
    field_simp
  apply hlim.congr'
  filter_upwards [Filter.Eventually.filter_mono hl (eventually_ge_atTop 2)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [pairMoment_cutoff_eq]
  exact div_div_div_cancel_right₀ (mul_ne_zero hn0 hl0) _ _

lemma count_filter_limit_ne_coefficient {A : Set ℕ} {c : ℝ} {l : Filter ℕ} [NeBot l]
    (hl : l ≤ atTop) (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ¬ Tendsto (fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)) l (𝓝 c) := by
  intro hcount
  have h1 := pair_moment_limit_filter hl hc h hcount 1 (by norm_num)
  have h2 := pair_moment_limit_filter hl hc h hcount 2 (by norm_num)
  have h3 := pair_moment_limit_filter hl hc h hcount 3 (by norm_num)
  have h4 := pair_moment_limit_filter hl hc h hcount 4 (by norm_num)
  have hh := (((h4.sub ((h1.const_mul 4).mul h3)).add
    (((h1.pow 2).const_mul 10).mul h2)).sub ((h1.pow 4).const_mul 5)).sub
      ((h2.pow 2).const_mul 2)
  norm_num at hh
  have hnon := ge_of_tendsto hh (Filter.Eventually.of_forall
    (fun n ↦ pair_raw_moment_inequality_all (cutoff A n) (fun a : ℕ ↦ (a : ℝ) / n)))
  norm_num at hnon

/-- The counting ratio must eventually exceed the representation coefficient by a fixed gap.
The gap may depend on the hypothetical witness. -/
lemma counting_coefficient_gap {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      c + δ ≤ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n) := by
  classical
  let R : ℕ → ℝ := fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)
  by_contra hnot
  have hbad (ε : ℝ) (hε : 0 < ε) : ∃ᶠ n in atTop, R n < c + ε := by
    change ¬ (∀ᶠ n in atTop, ¬ R n < c + ε)
    intro hh
    apply hnot
    exact ⟨ε, hε, hh.mono (fun n hn ↦ le_of_not_gt hn)⟩
  have hchoose (k : ℕ) : ∃ n : ℕ, k ≤ n ∧ |R n - c| ≤ 1 / ((k : ℝ) + 1) := by
    have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have hlo : ∀ᶠ n in atTop, c - 1 / ((k : ℝ) + 1) ≤ R n :=
      (normalized_count_bounds h hε).mono (fun _ hn ↦ hn.1)
    obtain ⟨n, hnhi, hnlo, hnge⟩ :=
      ((hbad _ hε).and_eventually (hlo.and (eventually_ge_atTop k))).exists
    exact ⟨n, hnge, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  choose N hN hclose using hchoose
  have hNlim : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun k ↦ show id k ≤ N k from hN k) tendsto_id
  have habs : Tendsto (fun k ↦ |R (N k) - c|) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _) hclose tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k ↦ R (N k)) atTop (𝓝 c) :=
    tendsto_sub_nhds_zero_iff.mp ((tendsto_zero_iff_abs_tendsto_zero _).mpr habs)
  have hmap : Tendsto R (Filter.map N atTop) (𝓝 c) := Filter.tendsto_map' hlim
  exact count_filter_limit_ne_coefficient hNlim hc h hmap

end Erdos66PrefixGap
