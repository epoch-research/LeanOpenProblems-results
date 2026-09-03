import FormalConjecturesUtil
import Submission.CofactorReflection
import Submission.LogSavingEnergy

/-! The number of distinct largest-prime cofactors is smaller than
`N / (log N)^B` for every fixed B. This is a support estimate, not a bound
for the signed sums attached to the cofactor labels. -/

namespace Erdos371CofactorLabels

open Finset Filter Erdos371Cofactor
open scoped Topology

noncomputable def labels (N : ℕ) : Finset ℕ := (range N).image cofactor

lemma cofactor_factor_bound (n : ℕ) : cofactor n * P (cofactor n) ≤ n := by
  rcases n with _ | _ | n
  · simp [cofactor, P]
  · simp [cofactor, P]
  · have hp := Nat.prime_maxPrimeFac_of_one_lt (n+2) (by omega)
    have ha := cofactor_pos (n := n+2) (by omega)
    have he : P (cofactor (n+2)) ≤ P (n+2) := by
      have hh : max (P (cofactor (n+2))) (P (n+2)) = P (n+2) := by
        have hf := congrArg Nat.maxPrimeFac (cofactor_mul (n+2))
        rw [Nat.maxPrimeFac_mul ha.ne' hp.ne_zero, hp.maxPrimeFac_eq_self] at hf
        exact hf
      exact (le_max_left _ _).trans hh.le
    calc
      _ ≤ cofactor (n+2) * P (n+2) := Nat.mul_le_mul_left _ he
      _ = _ := cofactor_mul _

lemma mem_labels_bound {a N : ℕ} (ha : a ∈ labels N) :
    a < N ∧ a * P a < N := by
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  have hlt := mem_range.mp hn
  exact ⟨(Nat.div_le_self n (P n)).trans_lt hlt,
    (cofactor_factor_bound n).trans_lt hlt⟩

lemma labels_card_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (labels N).card ≤ N/K + 1 +
      ((range N).filter fun a => P a ≤ K).card := by
  have hs : labels N ⊆ range (N/K+1) ∪ (range N).filter (fun a => P a ≤ K) := by
    intro a ha
    obtain ⟨haN, hprod⟩ := mem_labels_bound ha
    by_cases hp : P a ≤ K
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr haN, hp⟩)
    · apply mem_union_left
      apply mem_range.mpr
      have hk : a*K ≤ N :=
        (Nat.mul_le_mul_left a (Nat.le_of_not_ge hp)).trans hprod.le
      have hdiv := (Nat.le_div_iff_mul_le hK).mpr hk
      omega
  simpa only [card_range] using
    (card_le_card hs).trans (card_union_le _ _)

lemma normalized_labels_bound (B : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((labels N).card:ℝ) * Real.log (N:ℝ)^B / N ≤
        2*Real.log (N:ℝ)^B/N +
        Real.log (N:ℝ)^B/(N:ℝ)^(Erdos371LogSavingEnergy.delta (B+1)/2) +
        1/Real.log (N:ℝ) := by
  let K := Erdos371LogSavingEnergy.cutoff (B+1)
  let δ := Erdos371LogSavingEnergy.delta (B+1)/2
  filter_upwards [Erdos371LogSavingEnergy.eventually_smooth_count_bound
    (m := B+1) (by omega), eventually_gt_atTop 1] with N hs hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hk : 0 < K N := Erdos371LogSavingEnergy.cutoff_pos hN
  have hb := labels_card_bound hk N
  have hb' : ((labels N).card:ℝ) ≤
      (N:ℝ)/(K N) + 2 + (N:ℝ)/(N:ℝ)^δ := by
    have hc : ((labels N).card:ℝ) ≤ (N/K N:ℕ) + 1 +
        (((range N).filter fun a => P a ≤ K N).card:ℝ) := by exact_mod_cast hb
    have hd : ((N/K N:ℕ):ℝ) ≤ (N:ℝ)/(K N) := Nat.cast_div_le
    change (((range N).filter fun a => P a ≤ K N).card:ℝ) ≤
      1+(N:ℝ)/(N:ℝ)^δ at hs
    linarith
  have hc : Real.log (N:ℝ)^B/(K N) ≤ 1/Real.log (N:ℝ) := by
    calc
      _ ≤ Real.log (N:ℝ)^B/(Real.log (N:ℝ)^(B+1)) :=
        div_le_div_of_nonneg_left (pow_nonneg hl.le B) (pow_pos hl _)
          (Nat.le_ceil _)
      _ = _ := by rw [pow_succ]; field_simp
  have he : ((N:ℝ)/(K N)+2+(N:ℝ)/(N:ℝ)^δ)*Real.log (N:ℝ)^B/N =
      2*Real.log (N:ℝ)^B/N + Real.log (N:ℝ)^B/(N:ℝ)^δ +
      Real.log (N:ℝ)^B/(K N) := by field_simp; ring
  calc
    _ ≤ ((N:ℝ)/(K N)+2+(N:ℝ)/(N:ℝ)^δ)*Real.log (N:ℝ)^B/N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb' (pow_nonneg hl.le B)) hn.le
    _ = _ := he
    _ ≤ _ := add_le_add le_rfl hc

/-- The support of all cofactor labels, not merely the inputs with a small
cofactor, admits an arbitrary fixed logarithmic saving. -/
theorem labels_log_pow_div_tendsto_zero (B : ℕ) :
    Tendsto (fun N : ℕ => ((labels N).card:ℝ)*Real.log (N:ℝ)^B/N)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => 2*Real.log (N:ℝ)^B/N) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero, Function.comp_def, one_mul, add_zero] using
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 B (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  have hd := (Erdos371LogSavingEnergy.delta_bounds (show 0 < B+1 by omega)).1
  have h2 : Tendsto (fun N : ℕ => Real.log (N:ℝ)^B /
      (N:ℝ)^(Erdos371LogSavingEnergy.delta (B+1)/2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (B:ℝ)
        (show 0 < Erdos371LogSavingEnergy.delta (B+1)/2 by positivity)).tendsto_div_nhds_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
  have h3 : Tendsto (fun N : ℕ => 1/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp
      Erdos371LogSavingEnergy.log_tendsto
  have hu := (h1.add h2).add h3
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => by positivity
  · exact normalized_labels_bound B

lemma shifted_labels_log_pow_div_tendsto_zero (B : ℕ) :
    Tendsto (fun N : ℕ => ((labels (N+1)).card:ℝ)*Real.log (N:ℝ)^B/N)
      atTop (𝓝 0) := by
  have hh := (labels_log_pow_div_tendsto_zero B).comp (tendsto_add_atTop_nat 1)
  have hu : Tendsto (fun N : ℕ =>
      2*(((labels (N+1)).card:ℝ)*Real.log (N+1:ℕ)^B/(N+1:ℕ))) atTop (𝓝 0) := by
    simpa using hh.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hn' : (0:ℝ) < (N+1:ℕ) := by positivity
    have hl : Real.log (N:ℝ) ≤ Real.log (N+1:ℕ) :=
      Real.log_le_log hn (by exact_mod_cast Nat.le_succ N)
    have hp := pow_le_pow_left₀ (Real.log_natCast_nonneg N) hl B
    have hm := mul_le_mul_of_nonneg_left hp
      (Nat.cast_nonneg (α := ℝ) (labels (N+1)).card)
    apply (div_le_iff₀ hn).mpr
    have hnp : (N+1:ℕ) ≤ 2*N := by omega
    have hnr : ((N+1:ℕ):ℝ) ≤ 2*N := by exact_mod_cast hnp
    have hpos : 0 ≤ ((labels (N+1)).card:ℝ)*Real.log (N+1:ℕ)^B := by positivity
    have hscale : ((labels (N+1)).card:ℝ)*Real.log (N+1:ℕ)^B ≤
        (2*(((labels (N+1)).card:ℝ)*Real.log (N+1:ℕ)^B/(N+1:ℕ)))*N := by
      rw [show (2*(((labels (N+1)).card:ℝ)*Real.log (N+1:ℕ)^B/(N+1:ℕ)))*N =
        (2*((labels (N+1)).card:ℝ)*Real.log (N+1:ℕ)^B*N)/(N+1:ℕ) by ring]
      apply (le_div_iff₀ hn').mpr
      nlinarith
    exact hm.trans hscale

end Erdos371CofactorLabels

#print axioms Erdos371CofactorLabels.labels_log_pow_div_tendsto_zero

#print axioms Erdos371CofactorLabels.shifted_labels_log_pow_div_tendsto_zero
