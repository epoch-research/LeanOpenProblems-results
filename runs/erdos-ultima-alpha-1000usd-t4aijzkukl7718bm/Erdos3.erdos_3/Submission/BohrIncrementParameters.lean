import Submission.SupportedBohrIncrement

/-! Explicit error parameters for the supported relative Bohr increment.
This does not supply the iteration or the all-length conjecture. -/
namespace Erdos3BohrIncrementParameters
open Finset Erdos3SupportedBohrIncrement Erdos3FiniteBohr Erdos3CorrelationSifting
  Erdos3AsymmetricSifting Erdos3BohrLocalAverages Erdos3LocalCorrelationCentering
  Erdos3CrootSisaskL2
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3000000

def walkSteps (m : ℕ) : ℕ := m+10
def sampleAccuracy (m : ℕ) : ℕ := 1024*walkSteps m
def sampleCount (m : ℕ) : ℕ := 256*m^4*(sampleAccuracy m)^2
def stabilityDenominator (m R : ℕ) : ℕ := 1024*2^m*4^(R+1)
noncomputable def spectralTolerance (R : ℕ) : ℝ := 1/(4 : ℝ)^(R+1)
noncomputable def translationTolerance (m R : ℕ) : ℝ := 1/(stabilityDenominator m R : ℝ)
noncomputable def generatorRadius (m R : ℕ) : ℝ := 1/(2048*((R : ℝ)+1)*2^m)

lemma sampleAccuracy_pos (m : ℕ) : 0 < sampleAccuracy m := by
  unfold sampleAccuracy walkSteps
  positivity
lemma stabilityDenominator_pos (m R : ℕ) : 0 < stabilityDenominator m R := by
  unfold stabilityDenominator
  positivity
lemma spectralTolerance_pos (R : ℕ) : 0 < spectralTolerance R := by
  unfold spectralTolerance
  positivity
lemma translationTolerance_pos (m R : ℕ) : 0 < translationTolerance m R := by
  unfold translationTolerance
  exact one_div_pos.mpr (by exact_mod_cast stabilityDenominator_pos m R)
lemma generatorRadius_pos (m R : ℕ) : 0 < generatorRadius m R := by
  unfold generatorRadius
  positivity
lemma spectralTolerance_error (R : ℕ) : spectralTolerance R*4^(R+1) ≤ 1 := by
  unfold spectralTolerance
  rw [one_div_mul_cancel (by positivity : (4 : ℝ)^(R+1) ≠ 0)]

lemma sampling_loss (m : ℕ) :
    4*(walkSteps m : ℝ)/(sampleAccuracy m : ℝ) = 1/256 := by
  have hp : (walkSteps m : ℝ) ≠ 0 := by unfold walkSteps; positivity
  unfold sampleAccuracy
  push_cast
  field_simp
  norm_num

lemma spectral_tail_loss (m : ℕ) :
    (2 : ℝ)^m*(2*(1/2 : ℝ)^(2*walkSteps m)) ≤ 1/512 := by
  have he : (2 : ℝ)^m*(2*(1/2 : ℝ)^(2*walkSteps m)) =
      2*(1/2 : ℝ)^m*(1/4 : ℝ)^10 := by
    unfold walkSteps
    rw [mul_add, pow_add, pow_mul, pow_mul]
    rw [show ((1/2 : ℝ)^2) = 1/4 by norm_num]
    have hh : (2 : ℝ)^m*(1/4 : ℝ)^m = (1/2 : ℝ)^m := by
      rw [← mul_pow]
      norm_num
    calc
      _ = 2*((2 : ℝ)^m*(1/4 : ℝ)^m)*(1/4 : ℝ)^10 := by ring
      _ = _ := by rw [hh]
  rw [he]
  have hh : (1/2 : ℝ)^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

lemma phase_loss {d R : ℕ} (m : ℕ) (hd : d ≤ R) :
    (2 : ℝ)^m*(translationTolerance m R/spectralTolerance R+
      2*(d : ℝ)*generatorRadius m R) ≤ 1/512 := by
  have h2 : (2 : ℝ)^m ≠ 0 := by positivity
  have h4 : (4 : ℝ)^(R+1) ≠ 0 := by positivity
  have hR : (0 : ℝ) < (R : ℝ)+1 := by positivity
  have hratio : translationTolerance m R/spectralTolerance R = 1/(1024*(2 : ℝ)^m) := by
    unfold translationTolerance stabilityDenominator spectralTolerance
    push_cast
    field_simp
  rw [hratio]
  have hdR : (d : ℝ) ≤ (R : ℝ)+1 := by exact_mod_cast (show d ≤ R+1 by omega)
  have hh : 2*(d : ℝ)*generatorRadius m R ≤ 1/(1024*(2 : ℝ)^m) := by
    unfold generatorRadius
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1024*(2 : ℝ)^m)).mpr
    field_simp
    nlinarith
  calc
    _ ≤ (2 : ℝ)^m*(1/(1024*(2 : ℝ)^m)+1/(1024*(2 : ℝ)^m)) := by
      gcongr
    _ = _ := by field_simp; norm_num

/-- The chosen errors cost at most 1/128, uniformly in the old rank. -/
theorem total_loss {d R : ℕ} (m : ℕ) (hd : d ≤ R) :
    4*(walkSteps m : ℝ)/(sampleAccuracy m : ℝ)+(2 : ℝ)^m*
      (translationTolerance m R/spectralTolerance R+
        2*(d : ℝ)*generatorRadius m R+2*(1/2 : ℝ)^(2*walkSteps m)) ≤ 1/128 := by
  rw [sampling_loss]
  have hp := phase_loss m hd
  have ht := spectral_tail_loss m
  nlinarith

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A fixed relative increment, with all analytic error parameters specified. -/
theorem fixed_supported_increment (A B S T W : Finset G)
    (E : Finset (AddChar G ℂ)) {q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hS : S.Nonempty) (hT : T.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hfc : ∀ t, (33/32 : ℝ)*f t ≤
      Erdos3CorrelationMoments.corr (localNormalized A B) t/density B)
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ (1/128 : ℝ)*density S*density T)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W)
    {m R : ℕ} (hm : 0 < m) (hWS : W.card ≤ 2^(2*m)*S.card)
    (hgrowth : ((bohr E (q+h)).card : ℝ) ≤
      (1+translationTolerance m R)*((bohr E (q-h)).card : ℝ))
    (hR : 16*Real.log (4*(((T+bohr E q).card : ℝ)/T.card)^(sampleCount m)) < R+1) :
    ∃ D : Finset (AddChar G ℂ), D.card ≤ R ∧ ∃ x : G,
      (129/128 : ℝ)*relativeDensity A B ≤
        smooth (bohr (E ∪ D) (min h (generatorRadius m R))) (indicator A) x := by
  obtain ⟨D,hcard,x,hx⟩ := supported_bohr_increment A B S T W E hq hh
    (translationTolerance_pos m R).le (generatorRadius_pos m R).le hgrowth
    hA hAB hS hT f hf (by norm_num : (0 : ℝ) ≤ 33/32) hfc hbad hW hm
    (sampleAccuracy_pos m) hWS (walkSteps m) (spectralTolerance_pos R)
    (spectralTolerance_error R) hR
  refine ⟨D,hcard,x,?_⟩
  have hl := total_loss m hcard
  have hcoef : (129/128 : ℝ) ≤ (33/32 : ℝ)*(1-1/128-
      (4*(walkSteps m : ℝ)/(sampleAccuracy m : ℝ)+(2 : ℝ)^m*
        (translationTolerance m R/spectralTolerance R+
          2*(D.card : ℝ)*generatorRadius m R+2*(1/2 : ℝ)^(2*walkSteps m)))) := by
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (relativeDensity_pos A B hA hAB).le).trans hx

#print axioms total_loss
#print axioms fixed_supported_increment
end Erdos3BohrIncrementParameters
