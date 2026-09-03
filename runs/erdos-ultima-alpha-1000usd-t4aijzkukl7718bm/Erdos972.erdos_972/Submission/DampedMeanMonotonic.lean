import Submission.FullSmoothL1Obstruction

/-! Strict monotonicity of the positive-parameter Euler-product mean,
proved by a quantitative comparison on the even inputs. -/
namespace Erdos972DampedMeanMonotonic

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972DampedSingleMean Erdos972FixedDampedCorrelation
open Erdos972DampedMeanZeta Erdos972FullSmoothL1Obstruction

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma expFactor_mono {s t : ℝ} (hst : s ≤ t) (p : ℕ) :
    1-Real.exp (-s*Real.log p) ≤ 1-Real.exp (-t*Real.log p) := by
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hst (Real.log_natCast_nonneg p)
  linarith only [hh]

lemma expDivisorSum_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    expDivisorSum s n ≤ expDivisorSum t n := by
  by_cases hn : n = 0
  · simp [hn, expDivisorSum]
  rw [expDivisorSum_product s hn, expDivisorSum_product t hn]
  exact prod_le_prod (fun p _ => expFactor_nonneg hs p) (fun p _ => expFactor_mono hst p)

lemma expDivisorSum_two_mul (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    expDivisorSum t (2*n) = (1-Real.exp (-t*Real.log 2))*
      ∏ p ∈ n.primeFactors.erase 2, (1-Real.exp (-t*Real.log p)) := by
  have hpf : (2*n).primeFactors = insert 2 (n.primeFactors.erase 2) := by
    rw [Nat.primeFactors_mul (by norm_num) hn, Nat.prime_two.primeFactors]
    ext p
    simp
    tauto
  rw [expDivisorSum_product t (mul_ne_zero (by norm_num) hn), hpf,
    prod_insert (by simp)]
  norm_num only [Nat.cast_ofNat]

lemma expDivisorSum_le_erase_two {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : n ≠ 0) :
    expDivisorSum s n ≤ ∏ p ∈ n.primeFactors.erase 2, (1-Real.exp (-s*Real.log p)) := by
  rw [expDivisorSum_product s hn]
  by_cases h2 : 2 ∈ n.primeFactors
  · have hprod : 0 ≤ ∏ p ∈ n.primeFactors.erase 2, (1-Real.exp (-s*Real.log p)) :=
      prod_nonneg (fun p _ => expFactor_nonneg hs p)
    rw [← prod_erase_mul n.primeFactors (fun p : ℕ => 1-Real.exp (-s*Real.log p)) h2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (expFactor_le_one s 2) hprod
  · simp [h2]

/-- A positive Euler-factor gain occurs on every even input. -/
lemma even_difference_lower {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    (Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2))*expDivisorSum s n ≤
      expDivisorSum t (2*n)-expDivisorSum s (2*n) := by
  by_cases hn : n = 0
  · simp [hn, expDivisorSum]
  let Ps := ∏ p ∈ n.primeFactors.erase 2, (1-Real.exp (-s*Real.log p))
  let Pt := ∏ p ∈ n.primeFactors.erase 2, (1-Real.exp (-t*Real.log p))
  have hP : Ps ≤ Pt :=
    prod_le_prod (fun p _ => expFactor_nonneg hs p) (fun p _ => expFactor_mono hst p)
  have hfac := expFactor_nonneg (hs.trans hst) 2
  have hgap : 0 ≤ Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2) := by
    have hh := expFactor_mono hst 2
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  norm_num only [Nat.cast_ofNat] at hfac
  have h₁ := mul_le_mul_of_nonneg_left hP hfac
  have h₂ := mul_le_mul_of_nonneg_left (expDivisorSum_le_erase_two hs hn) hgap
  rw [expDivisorSum_two_mul t hn, expDivisorSum_two_mul s hn]
  change _ ≤ (1-Real.exp (-t*Real.log 2))*Pt-(1-Real.exp (-s*Real.log 2))*Ps
  change (Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2))*expDivisorSum s n ≤
    (Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2))*Ps at h₂
  nlinarith only [h₁, h₂]

lemma difference_prefix_lower {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (N : ℕ) :
    (Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2))*
        (∑ n ∈ Ioc 0 N, expDivisorSum s n) ≤
      ∑ n ∈ Ioc 0 (2*N), (expDivisorSum t n-expDivisorSum s n) := by
  classical
  calc
    _ = ∑ n ∈ Ioc 0 N,
        (Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2))*expDivisorSum s n := mul_sum ..
    _ ≤ ∑ n ∈ Ioc 0 N, (expDivisorSum t (2*n)-expDivisorSum s (2*n)) :=
      sum_le_sum (fun n _ => even_difference_lower hs hst n)
    _ = ∑ k ∈ (Ioc 0 N).image (fun n => 2*n), (expDivisorSum t k-expDivisorSum s k) := by
      rw [sum_image]
      intro a ha b hb hab
      change 2*a = 2*b at hab
      omega
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
        obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro k hk hnot
        exact sub_nonneg.mpr (expDivisorSum_mono hs hst k)

lemma dampedMean_pos {t : ℝ} (ht : 0 < t) : 0 < dampedMean t := by
  have hnonneg : 0 ≤ dampedMean t := by
    have hh := mul_nonneg (dampedMean_div_nonneg ht) ht.le
    rwa [div_mul_cancel₀ _ ht.ne'] at hh
  have hne : dampedMean t ≠ 0 := by
    intro hz
    have hh := zeta_mul_dampedMean ht
    rw [hz] at hh
    norm_num at hh
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Strict increase follows from the even-input gain and the ordinary
fixed-parameter means. -/
theorem dampedMean_strictMono {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    dampedMean s < dampedMean t := by
  have ht := hs.trans hst
  let c := Real.exp (-s*Real.log 2)-Real.exp (-t*Real.log 2)
  have hc : 0 < c := by
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    have hh := mul_lt_mul_of_pos_right hst (Real.log_pos (by norm_num : (1:ℝ) < 2))
    linarith only [hh]
  have htwo : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by omega : ∀ N : ℕ, N ≤ 2*N) tendsto_id
  have hl := (expDivisorSum_mean_tendsto hs).const_mul (c/2)
  have hr := ((expDivisorSum_mean_tendsto ht).sub (expDivisorSum_mean_tendsto hs)).comp htwo
  have hbound : ∀ᶠ N : ℕ in atTop,
      c/2*((∑ n ∈ Ioc 0 N, expDivisorSum s n)/(N:ℝ)) ≤
        (∑ n ∈ Ioc 0 (2*N), expDivisorSum t n)/(2*N:ℕ)-
          (∑ n ∈ Ioc 0 (2*N), expDivisorSum s n)/(2*N:ℕ) := by
    filter_upwards with N
    have hh := div_le_div_of_nonneg_right (difference_prefix_lower hs.le hst.le N)
      (Nat.cast_nonneg (α := ℝ) (2*N))
    change c*(∑ n ∈ Ioc 0 N, expDivisorSum s n)/((2*N:ℕ):ℝ) ≤ _ at hh
    rw [sum_sub_distrib] at hh
    convert hh using 1 <;> push_cast <;> ring
  have hlim := le_of_tendsto_of_tendsto hl hr hbound
  have hp : 0 < c/2*dampedMean s := mul_pos (div_pos hc (by norm_num)) (dampedMean_pos hs)
  linarith only [hlim, hp]

#print axioms even_difference_lower
#print axioms dampedMean_strictMono

end Erdos972DampedMeanMonotonic
