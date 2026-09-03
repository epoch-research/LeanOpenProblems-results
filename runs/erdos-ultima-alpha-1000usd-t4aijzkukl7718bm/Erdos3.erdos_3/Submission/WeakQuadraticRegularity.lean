import Submission.ClippedWeakRegularity
import Submission.QuadraticAverageDetectors
import Submission.NormalizedQuadraticPowerBounds

/-! An unconditional weak U3 regularity theorem on finite abelian groups with
bijective doubling. The approximant is a clipped combination of bounded local
quadratic averages, not yet a single equidistributed polynomial factor. -/
namespace Erdos3WeakQuadraticRegularity
open Finset Erdos3ClippedWeakRegularity Erdos3QuadraticAverageDetectors
  Erdos3NormalizedQuadraticInverse Erdos3NormalizedQuadraticPowerBounds Erdos3FiniteUniformity
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- No approximation hypothesis is assumed here: the bounded quadratic-average
detectors are obtained from the proved normalized local U3 inverse. -/
theorem weak_U3_regularity (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ l : List (G → ℝ), l.length ≤ ⌈(𝔼 x : G, f x)/(normalizedCorrelation δ)^2⌉₊+1 ∧
      (∀ ψ ∈ l, IsQuadraticAverageTest (normalizedRank δ) ψ) ∧
      uniformityPower 2 (fun x ↦ ((f x-clippedSum (normalizedCorrelation δ) l x : ℝ) : ℂ)) ≤ δ := by
  apply clipped_weak_regularity {ψ | IsQuadraticAverageTest (normalizedRank δ) ψ}
    (fun r ↦ uniformityPower 2 (fun x ↦ (r x : ℂ)) ≤ δ) f hf (normalizedCorrelation_pos hδ)
    (fun ψ hψ x ↦ quadraticAverageTest_bound _ ψ hψ x)
  intro r hr hnot
  exact large_U3_real_detector h2 r hr hδ (le_of_lt (lt_of_not_ge hnot))

noncomputable def regularityGain (δ : ℝ) : ℝ := δ^1988534/correlationDenominator

lemma regularityGain_pos {δ : ℝ} (hδ : 0 < δ) : 0 < regularityGain δ :=
  div_pos (pow_pos hδ _) correlationDenominator_pos

lemma regularityGain_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    regularityGain δ ≤ normalizedCorrelation δ := normalizedCorrelation_power_lower hδ hδ1

lemma regularityGain_inverse_sq {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    a/(regularityGain δ)^2 = a*correlationDenominator^2*(1/δ)^3977068 := by
  unfold regularityGain
  simp only [div_pow,← pow_mul,div_div,one_div_pow]
  norm_num
  ring_nf
  simp only [inv_inv]
  ring

/-- The number of bounded tests is polynomial in inverse uniformity accuracy,
with an extra factor of the original mean density. Every test's Bohr rank is
bounded by normalizedRank(delta), itself polynomially bounded. -/
theorem polynomial_weak_U3_regularity (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ l : List (G → ℝ),
      (l.length : ℝ) ≤ (𝔼 x : G, f x)*correlationDenominator^2*(1/δ)^3977068+2 ∧
      (∀ ψ ∈ l, IsQuadraticAverageTest (normalizedRank δ) ψ) ∧
      (∀ x, 0 ≤ clippedSum (regularityGain δ) l x ∧ clippedSum (regularityGain δ) l x ≤ 1) ∧
      uniformityPower 2 (fun x ↦ ((f x-clippedSum (regularityGain δ) l x : ℝ) : ℂ)) ≤ δ := by
  have hdet : ∀ r : G → ℝ, (∀ x, |r x| ≤ 1) →
      ¬ (uniformityPower 2 (fun x ↦ (r x : ℂ)) ≤ δ) →
      ∃ ψ ∈ {ψ | IsQuadraticAverageTest (normalizedRank δ) ψ}, regularityGain δ ≤ 𝔼 x : G, r x*ψ x := by
    intro r hr hnot
    obtain ⟨ψ,hψ,hcorr⟩ := large_U3_real_detector h2 r hr hδ (le_of_lt (lt_of_not_ge hnot))
    exact ⟨ψ,hψ,(regularityGain_le hδ hδ1).trans hcorr⟩
  obtain ⟨l,hlen,hl,hU⟩ := clipped_weak_regularity {ψ | IsQuadraticAverageTest (normalizedRank δ) ψ}
    (fun r ↦ uniformityPower 2 (fun x ↦ (r x : ℂ)) ≤ δ) f hf (regularityGain_pos hδ)
    (fun ψ hψ x ↦ quadraticAverageTest_bound _ ψ hψ x) hdet
  refine ⟨l,?_,hl,fun x ↦ clippedSum_bounds _ l x,hU⟩
  have hx : 0 ≤ (𝔼 x : G, f x)/(regularityGain δ)^2 :=
    div_nonneg (expect_nonneg (fun x _ ↦ (hf x).1)) (sq_nonneg _)
  have hc := Nat.ceil_lt_add_one hx
  have hlenR : (l.length : ℝ) ≤ (⌈(𝔼 x : G, f x)/(regularityGain δ)^2⌉₊ : ℝ)+1 := by
    exact_mod_cast hlen
  rw [regularityGain_inverse_sq hδ] at hc hlenR
  linarith

#print axioms weak_U3_regularity
#print axioms polynomial_weak_U3_regularity
end Erdos3WeakQuadraticRegularity
