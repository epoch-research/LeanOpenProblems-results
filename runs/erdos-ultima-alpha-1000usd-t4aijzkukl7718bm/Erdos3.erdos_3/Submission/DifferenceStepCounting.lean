import Submission.StepWeightedCounting
import Submission.DoubledWeights
import Submission.RelativeSpectrumPhase

/-! Counting with the normalized difference distribution of a finite set.
The Fourier mass is exactly the reciprocal density, giving an explicit and
honest local-to-global uniformity error. -/
namespace Erdos3DifferenceStepCounting
open Finset Erdos3StepWeightedCounting Erdos3FiniteFourier
  Erdos3FourierMultilinearTransfer Erdos3QuadraticFourAPBarrier
  Erdos3CorrelationSifting Erdos3CorrelationMoments Erdos3DoubledWeights
  Erdos3RelativeSpectrumPhase Erdos3FiniteUniformity Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma fourierMass_complexCorr (f : G → ℂ) :
    fourierMass (complexCorr f) = 𝔼 x : G, ‖f x‖^2 := by
  unfold fourierMass
  simp only [hat_complexCorr,Complex.norm_real,Real.norm_eq_abs,abs_pow,sq_abs]
  exact parseval f

lemma normalized_sq_expect (B : Finset G) (hB : B.Nonempty) :
    (𝔼 x : G, (normalized B x)^2) = 1/density B := by
  have he (x : G) : (normalized B x)^2 = normalized B x/density B := by
    by_cases hx : x ∈ B <;> simp [normalized,indicator,hx,pow_two,div_eq_mul_inv]
  simp only [he,← expect_div,expect_normalized B hB]

noncomputable def diffWeight (B : Finset G) (d : G) : ℂ := corr (normalized B) d

lemma diffWeight_complexCorr (B : Finset G) :
    diffWeight B = complexCorr (fun x ↦ (normalized B x : ℂ)) := by
  funext d
  simp only [diffWeight,corr,complexCorr,Complex.ofReal_expect,Complex.ofReal_mul,Complex.conj_ofReal]
  apply expect_congr rfl
  intro x _
  ring

/-- The exact Fourier mass, not just an upper bound. -/
theorem diffWeight_fourierMass (B : Finset G) (hB : B.Nonempty) :
    fourierMass (diffWeight B) = 1/density B := by
  rw [diffWeight_complexCorr,fourierMass_complexCorr]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact normalized_sq_expect B hB

lemma diffWeight_nonneg (B : Finset G) (d : G) : 0 ≤ (diffWeight B d).re := by
  change 0 ≤ corr (normalized B) d
  exact expect_nonneg (fun x _ ↦ mul_nonneg (normalized_nonneg B x) (normalized_nonneg B (x+d)))

lemma diffWeight_support (B : Finset G) {d : G} (hd : diffWeight B d ≠ 0) :
    ∃ b ∈ B, ∃ c ∈ B, d = c-b := by
  apply corr_normalized_nonzero B
  intro h
  apply hd
  simp only [diffWeight,h,Complex.ofReal_zero]

/-- Normalized correlation is precisely the probability distribution of c-b,
where b and c are chosen independently and uniformly from B. -/
theorem diffWeight_pairing (B : Finset G) (hB : B.Nonempty) (H : G → ℂ) :
    (𝔼 d : G, diffWeight B d*H d) = 𝔼 b : B, 𝔼 c : B, H ((c : G)-b) := by
  have he (d : G) : diffWeight B d*H d =
      𝔼 b : G, (normalized B b : ℂ)*((normalized B (b+d) : ℂ)*H d) := by
    simp only [diffWeight,corr,Complex.ofReal_expect,Complex.ofReal_mul,expect_mul,mul_assoc]
  simp only [he]
  rw [expect_comm]
  have ht (b : G) : (𝔼 d : G, (normalized B b : ℂ)*((normalized B (b+d) : ℂ)*H d)) =
      (normalized B b : ℂ)*(𝔼 c : G, (normalized B c : ℂ)*H (c-b)) := by
    rw [← mul_expect]
    congr 1
    exact Fintype.expect_equiv (Equiv.addLeft b) _ _ (fun d ↦ by
      change (normalized B (b+d) : ℂ)*H d = (normalized B (b+d) : ℂ)*H ((b+d)-b)
      rw [show (b+d)-b = d by abel])
  simp only [ht,expect_normalized_mul_complex B hB]

lemma diffWeight_mean (B : Finset G) (hB : B.Nonempty) :
    (𝔼 d : G, diffWeight B d) = 1 := by
  letI : Nonempty B := hB.to_subtype
  simpa only [mul_one,Fintype.expect_const] using diffWeight_pairing B hB (fun _ ↦ 1)

lemma diffWeight_bohr_support (D : Finset (AddChar G ℂ)) (r : ℝ)
    {d : G} (hd : diffWeight (bohr D r) d ≠ 0) : d ∈ bohr D (2*r) := by
  obtain ⟨b,hb,c,hc,rfl⟩ := diffWeight_support (bohr D r) hd
  simpa only [sub_eq_add_neg,two_mul] using bohr_add hc (bohr_neg hb)

variable {F : Type*} [Field F] [Fintype F]

noncomputable def differenceAverage {k : ℕ} (B : Finset F) (v : Fin k → F)
    (f : Fin k → F → ℂ) : ℂ :=
  𝔼 b : B, 𝔼 c : B, 𝔼 x : F, ∏ i : Fin k, f i (x+v i*((c : F)-b))

lemma differenceAverage_eq_weighted {k : ℕ} (B : Finset F) (hB : B.Nonempty)
    (v : Fin k → F) (f : Fin k → F → ℂ) :
    differenceAverage B v f = weightedLinearAverage v f (diffWeight B) :=
  (diffWeight_pairing B hB (fun d ↦ 𝔼 x : F, ∏ i : Fin k, f i (x+v i*d))).symm

/-- The global U^(k-1) residual controls counts with steps sampled from B-B,
with an explicit loss of 1/density(B). -/
theorem difference_counting_bound (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v) (f g : F → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hfg : ∀ x, ‖f x-g x‖ ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower (n+1) (fun x ↦ f x-g x) ≤ η^(2^(n+2))) :
    ‖differenceAverage B v (fun _ ↦ f)-differenceAverage B v (fun _ ↦ g)‖ ≤
      ((n+3 : ℕ)*η)/density B := by
  rw [differenceAverage_eq_weighted B hB,differenceAverage_eq_weighted B hB]
  have h := weighted_counting_difference n v hv f g (diffWeight B) hf hg hfg hη hU
  rw [diffWeight_fourierMass B hB] at h
  convert h using 1 <;> ring

#print axioms diffWeight_fourierMass
#print axioms diffWeight_pairing
#print axioms difference_counting_bound
end Erdos3DifferenceStepCounting
