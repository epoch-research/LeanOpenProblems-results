import Submission.SetIntervalReplacementExplore

/-! Arbitrarily late cardinality-preserving reflection patches with large
normalized representation counts. -/
namespace Erdos66LargeReflectionPatch
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66Counting Erdos66ReflectionRoundingPatch Erdos66FlatProfileWindows
  Erdos66SetIntervalReplacement
open scoped Topology Classical
set_option maxHeartbeats 2000000

noncomputable abbrev base : Set ℕ := roundedSet profile

lemma base_count_discrepancy (N : ℕ) :
    |(count base N : ℝ)-cumulative profile N| ≤ 1 := by
  rw [count_sum]
  exact (by simpa only [Finset.sum_sub_distrib] using
    rounded_prefix_discrepancy profile (fun n ↦ ⟨profile_nonneg n,profile_le_one n⟩) N)

lemma interval_card_lower (a w R : ℕ) (hR : a+w ≤ R) :
    (w : ℝ)*profile R-2 ≤ (intervalPart base a (a+w)).card := by
  have he := (abs_le.mp (local_count_error base profile 1 base_count_discrepancy a (a+w) (by omega))).1
  have hs := Finset.sum_le_sum (s := Finset.Ico a (a+w)) (f := fun _ ↦ profile R)
    (g := profile) (by
      intro i hi
      have hh := Finset.mem_Ico.mp hi
      exact profile_antitone (by omega))
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Ico,Nat.add_sub_cancel_left] at hs
  linarith

lemma eventual_log_peak_budget (M : ℕ) :
    ∀ᶠ k : ℕ in atTop, (M : ℝ)*(Real.log 6+32*Real.log (k : ℝ)) ≤ (k : ℝ)^2-4 := by
  have hdecay : Tendsto (fun k : ℕ ↦ (M : ℝ)*(Real.log 6+32*Real.log (k : ℝ))/(k : ℝ))
      atTop (𝓝 0) := by
    have h₁ := (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (Real.log 6)
    have h₂ := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 32
    have hh := (h₁.add h₂).const_mul (M : ℝ)
    simpa only [Function.comp_def,id_eq,mul_zero,add_zero,add_div,mul_div_assoc] using hh
  filter_upwards [eventually_ge_atTop 6,hdecay.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with k hk hh
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have ht := (div_lt_one (by linarith : (0 : ℝ) < k)).mp hh
  nlinarith

theorem exists_large_patch (T M : ℕ) :
    ∃ (L W : ℕ) (G : Finset ℕ), T ≤ L ∧ 0 < W ∧
      G ⊆ Finset.Ico (L+W) (L+2*W) ∧
      G.card = (intervalPart base (L+W) (L+2*W)).card ∧
      (∀ N : ℕ, |((G∩Finset.range N).card : ℝ)-
        ((intervalPart base (L+W) (L+2*W)∩Finset.range N).card : ℝ)| ≤ 10) ∧
      2 ≤ 2*L+2*W-1 ∧
      (M : ℝ) ≤ (sumRep ((intervalPart base L (L+W)∪G : Finset ℕ) : Set ℕ)
        (2*L+2*W-1) : ℝ)/Real.log ((2*L+2*W-1 : ℕ) : ℝ) := by
  obtain ⟨k,⟨⟨hk,hkT⟩,hH⟩,hbudget⟩ := (eventually_ge_atTop 6 |>.and
    (eventually_ge_atTop T) |>.and eventually_harmonic_polynomial_bound |>.and
    (eventual_log_peak_budget M)).exists
  obtain ⟨L,hL,hR,hosc,hmass⟩ := exists_flat_profile_window k hk hH
  let W := k^20
  have hW : 0 < W := pow_pos (by omega) _
  have hTL : T ≤ L := hkT.trans ((Nat.le_self_pow (by norm_num : 32≠0) k).trans hL)
  obtain ⟨G,hG,hGc,hGpref,hGrep⟩ := exists_reflection_patch base profile 1 (by norm_num)
    base_count_discrepancy profile_antitone L W hW hosc
  have hleft := interval_card_lower L W (L+2*W) (by omega)
  have hright := interval_card_lower (L+W) W (L+2*W) (by omega)
  rw [show L+W+W=L+2*W by omega] at hright
  have hcount : (k : ℝ)^2-4 ≤ (sumRep ((intervalPart base L (L+W)∪G : Finset ℕ) : Set ℕ)
      (2*L+2*W-1) : ℝ) := by
    have hmin : (k : ℝ)^2/2-2 ≤
        (min (intervalPart base L (L+W)).card (intervalPart base (L+W) (L+2*W)).card : ℕ) := by
      rw [Nat.cast_min]
      exact le_min (by linarith) (by linarith)
    have hh : 2*(min (intervalPart base L (L+W)).card (intervalPart base (L+W) (L+2*W)).card : ℕ) ≤
        (sumRep ((intervalPart base L (L+W)∪G : Finset ℕ) : Set ℕ) (2*L+2*W-1) : ℝ) := by
      exact_mod_cast hGrep
    linarith
  have ht2 : 2 ≤ 2*L+2*W-1 := by omega
  have htbound : 2*L+2*W-1 ≤ 6*k^32 := by dsimp [W] at *; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog : Real.log ((2*L+2*W-1 : ℕ) : ℝ) ≤ Real.log 6+32*Real.log (k : ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < 2*L+2*W-1 by omega) :
      (0 : ℝ) < ((2*L+2*W-1 : ℕ) : ℝ)) (by exact_mod_cast htbound : ((2*L+2*W-1 : ℕ) : ℝ) ≤ ((6*k^32 : ℕ) : ℝ))
    push_cast at hh
    rw [Real.log_mul (by norm_num) (pow_pos hk0 32).ne',Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  refine ⟨L,W,G,hTL,hW,hG,hGc,?_,ht2,?_⟩
  · simpa only [show (8 : ℝ)*1+2=10 by norm_num] using hGpref
  · apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < 2*L+2*W-1 by omega)))).mpr
    exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)).trans (hbudget.trans hcount)

end Erdos66LargeReflectionPatch
