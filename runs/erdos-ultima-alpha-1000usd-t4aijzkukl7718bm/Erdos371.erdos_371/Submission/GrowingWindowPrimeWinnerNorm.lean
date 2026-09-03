import Submission.GrowingWindowLargestPrimeHalf
import Submission.HarmonicPrimeWinnerColours
import Submission.VariableSupportSchur
import Submission.PrimeWinnerHarmonicLimits

/-! Uniform l1 cancellation of prime-winner currents on every interval of
diverging harmonic mass. The fixed-ratio unnormalized limit remains open. -/
namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

/-- Arbitrary fixed colours on the winning prime can be retained on moving
harmonic windows. Their harmonic mass must tend to infinity. -/
theorem primeWinner_coloured_growing_harmonic_zero (g : ℕ → Bool)
    (w : Bool → ℝ) (hw : ∀ b, |w b|≤1) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun n => factorSign n*w (g (primeWinner n)))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_shifted_harmonic_approximation
    (ε/2) (by positivity) A M hH
  let L (n : ℕ) := (localPrimeLabel Q n,g (Nat.maxPrimeFac n))
  let F (n : ℕ) := factorSign n*w (g (primeWinner n))
  let G (n : ℕ) := colouredOrderSkew w (L n) (L (n+1))
  have hz : Tendsto (fun j => shiftedHarmonicMean (A j) (M j) G) atTop (𝓝 0) :=
    stable_finite_labels_shifted_harmonic_skew_zero L
      (primeColouredLabel_mean_dilation_defect_zero Q g) (colouredOrderSkew w)
      (colouredOrderSkew_swap w) (colouredOrderSkew_abs_le w hw) A M hH
  filter_upwards [happrox Q le_rfl,hz.abs.eventually_lt_const
    (show |(0 : ℝ)|<ε/2 by simpa using half_pos hε)] with j ha hs
  have herr := (shiftedHarmonicMean_abs_difference_le (A j) (M j) F G).trans
    ((shiftedHarmonicMean_mono (A j) (M j) _ _
      (colouredOrderSkew_approximation Q g w hw)).trans ha)
  have ht := abs_sub_le (shiftedHarmonicMean (A j) (M j) F)
    (shiftedHarmonicMean (A j) (M j) G) 0
  rw [Real.dist_eq,sub_zero]
  simp only [sub_zero] at ht
  change |shiftedHarmonicMean (A j) (M j) F|<ε
  linarith

noncomputable def shiftedPrimeWinnerCurrent (A M p : ℕ) : ℝ :=
  shiftedHarmonicMean A M (fun n => if primeWinner n=p then factorSign n else 0)

lemma shiftedPrimeWinnerCurrent_test (A M B : ℕ) (hB : A+M+2<B) (s : ℕ → ℝ) :
    (∑ p ∈ range B, s p*shiftedPrimeWinnerCurrent A M p) =
      shiftedHarmonicMean A M (fun n => s (primeWinner n)*factorSign n) := by
  classical
  unfold shiftedPrimeWinnerCurrent shiftedHarmonicMean shiftedHarmonicRaw
  simp only [← mul_div_assoc,mul_sum,← sum_div]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn' := mem_range.mp hn
  have hb : primeWinner (A+n+1)<B := by
    have hh : primeWinner (A+n+1)≤A+n+1+1 :=
      max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
    omega
  rw [sum_eq_single (primeWinner (A+n+1))]
  · simp
  · intro p hp hne
    rw [if_neg (Ne.symm hne)]
    simp
  · intro hp
    exact False.elim (hp (mem_range.mpr hb))

lemma primeWinner_sign_test_growing_harmonic_zero (s : ℕ → ℝ)
    (hs : ∀ p, s p=1 ∨ s p= -1) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun n => s (primeWinner n)*factorSign n)) atTop (𝓝 0) := by
  classical
  let g (p : ℕ) : Bool := decide (s p=1)
  let w (b : Bool) : ℝ := if b then 1 else -1
  have he (p : ℕ) : w (g p)=s p := by
    rcases hs p with h|h <;> norm_num [w,g,h]
  have hw (b : Bool) : |w b|≤1 := by cases b <;> norm_num [w]
  simpa only [he,mul_comm] using
    primeWinner_coloured_growing_harmonic_zero g w hw A M hH

/-- Absolute values are taken separately for every prime winner, BEFORE
summing over the labels. The normalization is the full harmonic mass. -/
theorem primeWinner_growing_harmonic_l1_zero (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => ∑ p ∈ range (A j+M j+3),
      |shiftedPrimeWinnerCurrent (A j) (M j) p|) atTop (𝓝 0) := by
  apply variable_cutoff_schur_of_sign_tests
    (fun j p => shiftedPrimeWinnerCurrent (A j) (M j) p)
    (fun j => A j+M j+3)
  intro s hs
  have h := primeWinner_sign_test_growing_harmonic_zero s hs A M hH
  apply h.congr
  intro j
  exact (shiftedPrimeWinnerCurrent_test (A j) (M j) (A j+M j+3) (by omega) s).symm

/-- The l1 cancellation is uniform over ALL intervals of sufficiently large
harmonic mass. The mass threshold is not a bound on an ordinary endpoint. -/
theorem primeWinner_uniform_long_harmonic_l1 (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℝ, 0<R ∧ ∀ A M : ℕ, R≤shiftedHarmonicMass A M →
      (∑ p ∈ range (A+M+3), |shiftedPrimeWinnerCurrent A M p|)<ε := by
  by_contra h
  push_neg at h
  have hn (j : ℕ) : ∃ A M : ℕ, (j+1 : ℝ)≤shiftedHarmonicMass A M ∧
      ε≤∑ p ∈ range (A+M+3), |shiftedPrimeWinnerCurrent A M p| :=
    h (j+1) (by positivity)
  choose A M hmass hbad using hn
  have hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop :=
    tendsto_atTop_mono hmass
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))
  obtain ⟨j,hj⟩ := ((primeWinner_growing_harmonic_l1_zero A M hH).eventually_lt_const hε).exists
  exact (hbad j).not_gt hj

lemma shiftedPrimeWinnerCurrent_bounded_test (A M : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p, |w p|≤1) :
    |shiftedHarmonicMean A M (fun n => w (primeWinner n)*factorSign n)| ≤
      ∑ p ∈ range (A+M+3), |shiftedPrimeWinnerCurrent A M p| := by
  rw [← shiftedPrimeWinnerCurrent_test A M (A+M+3) (by omega) w]
  calc
    _ ≤ ∑ p ∈ range (A+M+3), |w p*shiftedPrimeWinnerCurrent A M p| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro p _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hw p)

/-- Even endpoint-dependent prime weights are allowed after the l1 upgrade. -/
theorem primeWinner_moving_weights_growing_harmonic_zero (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (w : ℕ → ℕ → ℝ) (hw : ∀ j p, |w j p|≤1) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun n => w j (primeWinner n)*factorSign n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (primeWinner_growing_harmonic_l1_zero A M hH)
  intro j
  simpa only [Real.norm_eq_abs] using
    shiftedPrimeWinnerCurrent_bounded_test (A j) (M j) (w j) (hw j)

lemma positiveRawSum_primeWinner_eq (p T : ℕ) :
    positiveRawSum T (fun n => if primeWinner n=p then factorSign n else 0) =
      rawPrimeWinnerHarmonic p (T+1) := by
  rw [positiveRawSum,show Icc 1 T=Ico 1 (T+1) by ext n; simp,
    sum_Ico_eq_sub _ (by omega)]
  simp only [rawPrimeWinnerHarmonic,primeWinnerHarmonicTerm,ite_div,zero_div,
    sum_range_one,Nat.cast_zero,div_zero,ite_self,sub_zero]

/-- Exact conversion to the previously defined unnormalized harmonic
currents. No change of the mass normalization is made. -/
lemma shiftedPrimeWinnerCurrent_eq_raw_window (A M p : ℕ) :
    shiftedPrimeWinnerCurrent A M p =
      (rawPrimeWinnerHarmonic p (A+M+2)-rawPrimeWinnerHarmonic p (A+1))/
        shiftedHarmonicMass A M := by
  rw [shiftedPrimeWinnerCurrent,shiftedHarmonicMean,shiftedHarmonicRaw_eq_sub,
    positiveRawSum_primeWinner_eq,positiveRawSum_primeWinner_eq]


lemma shiftedPrimeWinnerCurrent_zero_above (A M p : ℕ) (hp : A+M+2<p) :
    shiftedPrimeWinnerCurrent A M p=0 := by
  unfold shiftedPrimeWinnerCurrent shiftedHarmonicMean shiftedHarmonicRaw
  suffices h : (∑ n ∈ range (M+1),
      (if primeWinner (A+n+1)=p then factorSign (A+n+1) else 0)/(A+n+1 : ℝ))=0 by
    rw [h,zero_div]
  apply sum_eq_zero
  intro n hn
  have hn' := mem_range.mp hn
  have hh : primeWinner (A+n+1)≤A+n+1+1 :=
    max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
  rw [if_neg (by omega : primeWinner (A+n+1)≠p),zero_div]

lemma shiftedPrimeWinnerCurrent_l1_eq_tsum (A M : ℕ) :
    (∑ p ∈ range (A+M+3), |shiftedPrimeWinnerCurrent A M p|) =
      ∑' p : ℕ, |shiftedPrimeWinnerCurrent A M p| := by
  classical
  symm
  apply tsum_eq_sum
  intro p hp
  rw [shiftedPrimeWinnerCurrent_zero_above A M p
    (by simp only [mem_range,not_lt] at hp; omega),abs_zero]

/-- The growing-window result as convergence in the full prime-indexed l1 norm. -/
theorem primeWinner_growing_harmonic_tsum_zero (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => ∑' p : ℕ, |shiftedPrimeWinnerCurrent (A j) (M j) p|)
      atTop (𝓝 0) := by
  simpa only [← shiftedPrimeWinnerCurrent_l1_eq_tsum] using
    primeWinner_growing_harmonic_l1_zero A M hH

/-- A single mass threshold works for all intervals and all bounded prime
weights. The weights may be chosen after the interval is known. -/
theorem primeWinner_uniform_long_harmonic_weights (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℝ, 0<R ∧ ∀ A M : ℕ, R≤shiftedHarmonicMass A M →
      ∀ w : ℕ → ℝ, (∀ p, |w p|≤1) →
        |shiftedHarmonicMean A M (fun n => w (primeWinner n)*factorSign n)|<ε := by
  obtain ⟨R,hR,hbound⟩ := primeWinner_uniform_long_harmonic_l1 ε hε
  exact ⟨R,hR,fun A M hm w hw =>
    (shiftedPrimeWinnerCurrent_bounded_test A M w hw).trans_lt (hbound A M hm)⟩

#print axioms primeWinner_growing_harmonic_tsum_zero
#print axioms primeWinner_uniform_long_harmonic_weights

#print axioms primeWinner_growing_harmonic_l1_zero
#print axioms primeWinner_uniform_long_harmonic_l1
#print axioms primeWinner_moving_weights_growing_harmonic_zero
end Erdos371
