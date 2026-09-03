import Submission.NormalizedQuadraticInverse

/-! Converts normalized averaged local quadratic correlation into a globally
bounded real correlation detector. No Bohr-density loss occurs: centers are
averaged after translation, and correlation weights give an exact square. -/
namespace Erdos3QuadraticAverageDetectors
open Finset Erdos3NormalizedQuadraticInverse Erdos3FiniteUniformity Erdos3FiniteBohr
  Erdos3LocalQuadraticInverse Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def localPairing (B : Finset G) (q : G → G → ℂ) (f : G → ℝ) (a : G) : ℂ :=
  𝔼 y : B, (f (a+y) : ℂ)*conj (q a y)

noncomputable def complexAverage (B : Finset G) (q : G → G → ℂ) (b : G → ℂ) (x : G) : ℂ :=
  𝔼 y : B, b (x-y)*conj (q (x-y) y)

noncomputable def realAverage (B : Finset G) (q : G → G → ℂ) (b : G → ℂ) (x : G) : ℝ :=
  (complexAverage B q b x).re

lemma localPairing_norm (B : Finset G) (hB : B.Nonempty) (q : G → G → ℂ)
    (hq : ∀ a y, ‖q a y‖ = 1) (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) (a : G) :
    ‖localPairing B q f a‖ ≤ 1 := by
  letI : Nonempty B := hB.to_subtype
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro y _
  simpa only [norm_mul,Complex.norm_conj,hq,mul_one,Complex.norm_real,Real.norm_eq_abs] using hf (a+y)

lemma complexAverage_norm (B : Finset G) (hB : B.Nonempty) (q : G → G → ℂ)
    (hq : ∀ a y, ‖q a y‖ = 1) (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (x : G) :
    ‖complexAverage B q b x‖ ≤ 1 := by
  letI : Nonempty B := hB.to_subtype
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro y _
  simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hb (x-y)

lemma realAverage_abs (B : Finset G) (hB : B.Nonempty) (q : G → G → ℂ)
    (hq : ∀ a y, ‖q a y‖ = 1) (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (x : G) :
    |realAverage B q b x| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (complexAverage_norm B hB q hq b hb x)

lemma average_pairing_identity (B : Finset G) (q : G → G → ℂ) (b : G → ℂ) (f : G → ℝ) :
    (𝔼 x : G, (f x : ℂ)*complexAverage B q b x) =
      𝔼 a : G, b a*localPairing B q f a := by
  unfold complexAverage localPairing
  simp only [mul_expect]
  rw [expect_comm]
  have he (y : B) :
      (𝔼 x : G, (f x : ℂ)*(b (x-y)*conj (q (x-y) y))) =
      𝔼 a : G, b a*((f (a+y) : ℂ)*conj (q a y)) := by
    apply (Fintype.expect_equiv (Equiv.addRight (y : G)) _ _ ?_).symm
    intro a
    change b a*((f (a+y) : ℂ)*conj (q a y)) =
      (f (a+y) : ℂ)*(b ((a+y)-y)*conj (q ((a+y)-y) y))
    rw [show (a+(y : G))-(y : G) = a by abel]
    ring
  simp only [he]
  rw [expect_comm]

/-- Taking the center weight to be the conjugate local correlation converts
the averaged squared local correlation into an ordinary real pairing. -/
theorem realAverage_self_pairing (B : Finset G) (q : G → G → ℂ) (f : G → ℝ) :
    (𝔼 x : G, f x*realAverage B q (fun a ↦ conj (localPairing B q f a)) x) =
      𝔼 a : G, ‖localPairing B q f a‖^2 := by
  calc
    _ = (𝔼 x : G, (f x : ℂ)*complexAverage B q (fun a ↦ conj (localPairing B q f a)) x).re := by
      rw [expect_re]
      apply expect_congr rfl
      intro x _
      simp only [realAverage,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    _ = (𝔼 a : G, conj (localPairing B q f a)*localPairing B q f a).re :=
      congrArg Complex.re (average_pairing_identity B q _ f)
    _ = _ := by
      rw [expect_re]
      apply expect_congr rfl
      intro a _
      rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_re]

def IsQuadraticAverageTest (R : ℕ) (ψ : G → ℝ) : Prop :=
  ∃ D : Finset (AddChar G ℂ), ∃ q : G → G → ℂ, ∃ b : G → ℂ,
    D.card ≤ R ∧ (∀ a y, ‖q a y‖ = 1) ∧
    (∀ a, IsLocallyQuadratic (bohr D (1/16) : Set G) (q a)) ∧
    (∀ a, ‖b a‖ ≤ 1) ∧ ψ = realAverage (bohr D (1/16)) q b

lemma quadraticAverageTest_bound (R : ℕ) (ψ : G → ℝ) (hψ : IsQuadraticAverageTest R ψ) (x : G) :
    |ψ x| ≤ 1 := by
  obtain ⟨D,q,b,_,hq,_,hb,rfl⟩ := hψ
  exact realAverage_abs _ ⟨0,bohr_zero D (by norm_num)⟩ q hq b hb x

/-- A bounded real detector, with the same polynomial rank and correlation
parameters as the normalized local inverse theorem. -/
theorem large_U3_real_detector (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hU : δ ≤ uniformityPower 2 (fun x ↦ (f x : ℂ))) :
    ∃ ψ : G → ℝ, IsQuadraticAverageTest (normalizedRank δ) ψ ∧
      normalizedCorrelation δ ≤ 𝔼 x : G, f x*ψ x := by
  obtain ⟨D,q,hD,hq,hquad,hcorr⟩ := normalized_local_quadratic_inverse h2
    (fun x ↦ (f x : ℂ)) (fun x ↦ by simpa using hf x) hδ hU
  let B := bohr D (1/16)
  have hB : B.Nonempty := ⟨0,bohr_zero D (by norm_num)⟩
  let b : G → ℂ := fun a ↦ conj (localPairing B q f a)
  have hb (a : G) : ‖b a‖ ≤ 1 := by
    rw [show b a = conj (localPairing B q f a) from rfl,Complex.norm_conj]
    exact localPairing_norm B hB q hq f hf a
  refine ⟨realAverage B q b,⟨D,q,b,hD,hq,hquad,hb,rfl⟩,?_⟩
  change normalizedCorrelation δ ≤ 𝔼 x : G, f x*realAverage B q (fun a ↦ conj (localPairing B q f a)) x
  rw [realAverage_self_pairing]
  exact hcorr

#print axioms realAverage_self_pairing
#print axioms large_U3_real_detector
end Erdos3QuadraticAverageDetectors
