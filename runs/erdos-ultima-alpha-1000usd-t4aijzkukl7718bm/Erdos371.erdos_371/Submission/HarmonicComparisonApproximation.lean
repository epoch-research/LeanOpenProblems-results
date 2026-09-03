import Submission.PowerPrefixQuantization
import Submission.HarmonicStablePrimeTransfer
import Submission.DiagonalFullRoughCutoff

/-! Fine quantization of the actual comparison sign in harmonic mean. The
small-prefix harmonic mass is retained; a natural-density error at just the
largest endpoint would not suffice. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma harmonicPrefixLength_le (N : ℕ) (i : Fin (N+1)) : harmonicPrefixLength N i ≤ N+1 := by
  unfold harmonicPrefixLength
  split_ifs <;> omega

lemma harmonicPrefixLaw_short_length_mass (N Y : ℕ) (hY : Y ≤ N+1) :
    mean (harmonicPrefixLaw N) (fun i => if harmonicPrefixLength N i < Y then (1 : ℝ) else 0) ≤
      (harmonic Y : ℝ)/(harmonic (N+1) : ℝ) := by
  rw [mean_harmonicPrefixLaw N (fun k => if k<Y then (1 : ℝ) else 0)]
  simp only [if_neg (not_lt.mpr hY),zero_add,ite_div,zero_div]
  apply div_le_div_of_nonneg_right _ (harmonic_real_pos N).le
  rw [harmonic_real_sum,← sum_filter]
  calc
    _ ≤ ∑ k ∈ (range N).filter (fun k => k+1<Y), (1 : ℝ)/(k+1) := by
      apply sum_le_sum
      intro k hk
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        have := (mem_filter.mp hk).2
        simp only [mem_range]
        omega
      · intro k hk hnot
        positivity

lemma harmonicMean_sub (N : ℕ) (F G : ℕ → ℝ) :
    harmonicMean N (fun n => F n-G n) = harmonicMean N F-harmonicMean N G := by
  simp only [harmonicMean,sub_div,sum_sub_distrib]

lemma harmonicMean_const_mul (N : ℕ) (c : ℝ) (F : ℕ → ℝ) :
    harmonicMean N (fun n => c*F n) = c*harmonicMean N F := by
  simp only [harmonicMean,mul_div_assoc,← mul_sum]

lemma harmonicRangeMean_const_mul (N : ℕ) (c : ℝ) (F : ℕ → ℝ) :
    harmonicRangeMean N (fun n => c*F n) = c*harmonicRangeMean N F := by
  simp only [harmonicRangeMean,mul_div_assoc,← mul_sum]

lemma harmonicMean_range_error_two (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 2) :
    |harmonicRangeMean (N+1) F-harmonicMean (N+1) F| ≤ 4/(harmonic (N+1) : ℝ) := by
  have he := harmonicMean_range_error N (fun n => (1/2 : ℝ)*F n) (fun n => by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
    linarith [hF n])
  rw [harmonicMean_const_mul,harmonicRangeMean_const_mul,← mul_sub,abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ)<1/2)] at he
  convert (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;> ring

lemma harmonicMean_abs_le_abs_mean (N : ℕ) (F : ℕ → ℝ) :
    |harmonicMean (N+1) F| ≤ harmonicMean (N+1) (fun n => |F n|) := by
  rw [harmonicMean,abs_div,abs_of_pos (harmonic_real_pos N),harmonicMean]
  apply div_le_div_of_nonneg_right _ (harmonic_real_pos N).le
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply sum_congr rfl
  intro n hn
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma harmonicMean_abs_difference_le (N : ℕ) (F G : ℕ → ℝ) :
    |harmonicMean (N+1) F-harmonicMean (N+1) G| ≤
      harmonicMean (N+1) (fun n => |F n-G n|) := by
  rw [← harmonicMean_sub]
  exact harmonicMean_abs_le_abs_mean N _

end Erdos371.FiniteInformation

namespace Erdos371
open Finset Filter FiniteInformation FiniteSieve
open scoped Topology
set_option autoImplicit false

lemma rootRoughCutoff_le_self (k N : ℕ) (hN : 1 ≤ N) : rootRoughCutoff k N ≤ N := by
  unfold rootRoughCutoff ceilPowerCutoff
  apply Nat.ceil_le.mpr
  calc
    (N : ℝ)^(1/(k+1 : ℝ)) ≤ (N : ℝ)^((1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
        ((div_le_one (by positivity : (0 : ℝ)<k+1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
    _ = _ := Real.rpow_one _

lemma root_harmonic_ratio_eventually_le (k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (harmonic (rootRoughCutoff k (N+1)) : ℝ)/(harmonic (N+1) : ℝ) ≤
        1/Real.log (N+1 : ℝ)+2/(k+1 : ℝ) := by
  have hs := tendsto_add_atTop_nat 1
  filter_upwards [hs.eventually (rootRoughCutoff_log_eventually_le k),
    (rootRoughCutoff_atTop k |>.comp hs).eventually_ge_atTop 1,eventually_ge_atTop (1 : ℕ)]
    with N hlog hY hN
  let Y := rootRoughCutoff k (N+1)
  have hY0 : 0 < Y := lt_of_lt_of_le Nat.zero_lt_one hY
  have hl : 0 < Real.log (N+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N+1 by omega))
  have hden : Real.log (N+1 : ℝ) ≤ (harmonic (N+1) : ℝ) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ (N+1)))).trans
      (log_add_one_le_harmonic (N+1))
  have hlogY : Real.log (Y : ℝ) ≤ Real.log (Y+1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast hY0) (by linarith)
  have hlnon : 0 ≤ Real.log (Y+1 : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ Y+1 by omega))
  simp only [Nat.cast_add,Nat.cast_one] at hlog
  change Real.log (Y+1 : ℝ)/Real.log (N+1 : ℝ) ≤ 2/(k+1 : ℝ) at hlog
  have hnum : (harmonic Y : ℝ) ≤ 1+Real.log (Y+1 : ℝ) :=
    (harmonic_le_one_add_log Y).trans (by linarith)
  calc
    _ ≤ (1+Real.log (Y+1 : ℝ))/(harmonic (N+1) : ℝ) :=
      div_le_div_of_nonneg_right hnum (harmonic_real_pos N).le
    _ ≤ (1+Real.log (Y+1 : ℝ))/Real.log (N+1 : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hl hden
    _ ≤ _ := by
      rw [add_div]
      linarith

/-- A fixed positive-power prefix cutoff loses at most its explicitly bounded
harmonic mass. The quantization resolution is uniform over all finer Q. -/
theorem quantFactorSign_harmonic_range_power_bound (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ Q₀ > 0, ∀ᶠ N : ℕ in atTop, ∀ Q ≥ Q₀,
      harmonicRangeMean (N+1) (fun n => |factorSign n-quantFactorSign Q (N+1) n|) ≤
        η+4/(k+1 : ℝ)+2/Real.log (N+1 : ℝ) := by
  obtain ⟨Q₀,hQ₀,happrox⟩ := quantFactorSign_power_prefix_approximation (k+1) η hη
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp happrox
  have hs := tendsto_add_atTop_nat 1
  refine ⟨Q₀,hQ₀,?_⟩
  filter_upwards [(rootRoughCutoff_atTop k |>.comp hs).eventually_ge_atTop T₀,
    root_harmonic_ratio_eventually_le k] with N hY₀ hratio
  intro Q hQ
  let Y := rootRoughCutoff k (N+1)
  let F (n : ℕ) := |factorSign n-quantFactorSign Q (N+1) n|
  have hYle : Y ≤ N+1 := rootRoughCutoff_le_self k (N+1) (by omega)
  have he (i : Fin (N+1)) : prefixMean (harmonicPrefixLength N i) F ≤
      η+2*(if harmonicPrefixLength N i < Y then (1 : ℝ) else 0) := by
    by_cases hi : harmonicPrefixLength N i < Y
    · rw [if_pos hi]
      have hb : |prefixMean (harmonicPrefixLength N i) F| ≤ 2 :=
        abs_prefixMean_le _ (harmonicPrefixLength_pos N i) F 2 (fun n hn => by
          simpa only [F,abs_abs] using quantFactorSign_error_le_two Q (N+1) n)
      exact (le_abs_self _).trans (hb.trans (by linarith))
    · rw [if_neg hi,mul_zero,add_zero]
      apply hT₀ (harmonicPrefixLength N i) (hY₀.trans (not_lt.mp hi)) Q hQ (N+1)
        (harmonicPrefixLength_le N i)
      exact (rootRoughCutoff_power k (N+1)).trans (Nat.pow_le_pow_left (not_lt.mp hi) _)
  have hm := mean_mono (harmonicPrefixLaw N) _ _ he
  rw [mean_add,mean_const,mean_const_mul] at hm
  rw [harmonicPrefixLaw_representation] at hm
  change harmonicRangeMean (N+1) F ≤ _ at hm
  have hmass := harmonicPrefixLaw_short_length_mass N Y hYle
  change (harmonic Y : ℝ)/(harmonic (N+1) : ℝ) ≤ _ at hratio
  change harmonicRangeMean (N+1) F ≤ _
  calc
    _ ≤ η+2*((harmonic Y : ℝ)/(harmonic (N+1) : ℝ)) := by linarith
    _ ≤ η+2*(1/Real.log (N+1 : ℝ)+2/(k+1 : ℝ)) := by linarith
    _ = _ := by ring

/-- Uniform fine quantization of the actual sign in harmonic mean. This
uses control of all sufficiently long positive-power prefixes, not just one
natural-average approximation at N. -/
theorem quantFactorSign_harmonic_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ > 0, ∀ᶠ N : ℕ in atTop, ∀ Q ≥ Q₀,
      harmonicMean (N+1) (fun n => |factorSign n-quantFactorSign Q (N+1) n|) ≤ ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt ((16 : ℝ)/ε)
  have hfrac : 4/(k+1 : ℝ) < ε/4 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ)<k+1)).mpr
    have hm := (div_lt_iff₀ hε).mp hk
    nlinarith
  obtain ⟨Q₀,hQ₀,happrox⟩ := quantFactorSign_harmonic_range_power_bound k (ε/4) (by positivity)
  have hlog : Tendsto (fun N : ℕ => Real.log (N+1 : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one,Function.comp_def] using
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  have he : Tendsto (fun N : ℕ => (2 : ℝ)/Real.log (N+1 : ℝ)+4/(harmonic (N+1) : ℝ))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.div_atTop hlog).add
      (tendsto_const_nhds.div_atTop harmonic_real_tendsto) using 1
    norm_num
  refine ⟨Q₀,hQ₀,?_⟩
  filter_upwards [happrox,he.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N ha he
  intro Q hQ
  have hd := harmonicMean_range_error_two N
    (fun n => |factorSign n-quantFactorSign Q (N+1) n|)
    (fun n => by simpa only [abs_abs] using quantFactorSign_error_le_two Q (N+1) n)
  have hh := (abs_le.mp hd).1
  linarith [ha Q hQ]

#print axioms root_harmonic_ratio_eventually_le
#print axioms quantFactorSign_harmonic_range_power_bound
#print axioms quantFactorSign_harmonic_approximation
end Erdos371
