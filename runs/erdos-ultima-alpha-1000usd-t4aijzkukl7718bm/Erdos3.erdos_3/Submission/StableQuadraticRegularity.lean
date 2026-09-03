import Submission.WeakQuadraticRegularity
import Submission.VariableRadiusQuadraticInverse

/-! The weak U3 decomposition can use local quadratic averages on stable
Bohr radii, at any preselected stability tolerance, without worsening the
rank or correlation parameters. -/
namespace Erdos3StableQuadraticRegularity
open Finset Erdos3ClippedWeakRegularity Erdos3QuadraticAverageDetectors
  Erdos3WeakQuadraticRegularity Erdos3NormalizedQuadraticInverse
  Erdos3VariableRadiusQuadraticInverse Erdos3FiniteUniformity Erdos3FiniteBohr
  Erdos3LocalQuadraticInverse Erdos3RelativeStableBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def IsStableQuadraticAverageTest (R z : ℕ) (ψ : G → ℝ) : Prop :=
  ∃ D : Finset (AddChar G ℂ), ∃ r : ℝ, ∃ q : G → G → ℂ, ∃ b : G → ℂ,
    D.card ≤ R ∧ 1/64 ≤ r ∧ r ≤ 1/32 ∧ RelativeStable D z r ∧
    (∀ a y, ‖q a y‖ = 1) ∧
    (∀ a, IsLocallyQuadratic (bohr D (1/16) : Set G) (q a)) ∧
    (∀ a, ‖b a‖ ≤ 1) ∧ ψ = realAverage (bohr D r) q b

lemma stableQuadraticAverageTest_bound (R z : ℕ) (ψ : G → ℝ)
    (hψ : IsStableQuadraticAverageTest R z ψ) (x : G) : |ψ x| ≤ 1 := by
  obtain ⟨D,r,q,b,_,hr,_,_,hq,_,hb,rfl⟩ := hψ
  exact realAverage_abs _ ⟨0,bohr_zero D (by linarith)⟩ q hq b hb x

theorem large_U3_stable_real_detector (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hU : δ ≤ uniformityPower 2 (fun x ↦ (f x : ℂ))) {z : ℕ} (hz : 0 < z) :
    ∃ ψ : G → ℝ, IsStableQuadraticAverageTest (normalizedRank δ) z ψ ∧
      normalizedCorrelation δ ≤ 𝔼 x : G, f x*ψ x := by
  obtain ⟨D,r,q,hD,hr,hrmax,hstable,hq,hquad,hcorr⟩ := stable_radius_local_quadratic_inverse h2
    (fun x ↦ (f x : ℂ)) (fun x ↦ by simpa using hf x) hδ hU hz
  let B := bohr D r
  have hB : B.Nonempty := ⟨0,bohr_zero D (by linarith)⟩
  let b : G → ℂ := fun a ↦ conj (localPairing B q f a)
  have hb (a : G) : ‖b a‖ ≤ 1 := by
    rw [show b a = conj (localPairing B q f a) from rfl,Complex.norm_conj]
    exact localPairing_norm B hB q hq f hf a
  refine ⟨realAverage B q b,⟨D,r,q,b,hD,hr,hrmax,hstable,hq,hquad,hb,rfl⟩,?_⟩
  change normalizedCorrelation δ ≤ 𝔼 x : G, f x*realAverage B q (fun a ↦ conj (localPairing B q f a)) x
  rw [realAverage_self_pairing]
  exact hcorr

/-- The stability parameter is chosen independently of the ambient group and
before the decomposition. Its size does not enter the test-count or rank bound. -/
theorem stable_weak_U3_regularity (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z : ℕ} (hz : 0 < z) :
    ∃ l : List (G → ℝ), l.length ≤ ⌈(𝔼 x : G, f x)/(regularityGain δ)^2⌉₊+1 ∧
      (∀ ψ ∈ l, IsStableQuadraticAverageTest (normalizedRank δ) z ψ) ∧
      uniformityPower 2 (fun x ↦ ((f x-clippedSum (regularityGain δ) l x : ℝ) : ℂ)) ≤ δ := by
  apply clipped_weak_regularity {ψ | IsStableQuadraticAverageTest (normalizedRank δ) z ψ}
    (fun r ↦ uniformityPower 2 (fun x ↦ (r x : ℂ)) ≤ δ) f hf (regularityGain_pos hδ)
    (fun ψ hψ x ↦ stableQuadraticAverageTest_bound _ z ψ hψ x)
  intro r hr hnot
  obtain ⟨ψ,hψ,hcorr⟩ := large_U3_stable_real_detector h2 r hr hδ (le_of_lt (lt_of_not_ge hnot)) hz
  exact ⟨ψ,hψ,(regularityGain_le hδ hδ1).trans hcorr⟩

#print axioms large_U3_stable_real_detector
#print axioms stable_weak_U3_regularity
end Erdos3StableQuadraticRegularity
