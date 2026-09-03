import Submission.FiniteBesselSelection

/-! A common witness for two bounded targets. The target may be chosen
adversarially at each witness, permitting a simultaneous maximal selection. -/
namespace Erdos371.FiniteSieve
open Finset
variable {ι Ω : Type*}

theorem finite_bessel_two_target_selection (I : Finset ι) (hI : I.Nonempty)
    (X : Finset Ω) (hX : X.Nonempty) (G : Bool → Ω → ℝ) (W : ι → Ω → ℝ)
    (b : ι → Bool) (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε)
    (hsize : 4*((1 : ℝ)/I.card+η) < ε^2)
    (hG : ∀ t x, x ∈ X → |G t x| ≤ 1)
    (hW : ∀ i ∈ I, ∀ x ∈ X, |W i x| ≤ 1)
    (hGram : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → |∑ x ∈ X, W i x*W j x| ≤ η*X.card) :
    ∃ i ∈ I, |(∑ x ∈ X, G (b i) x*W i x)/(X.card : ℝ)| < ε := by
  have hIr : (0 : ℝ) < I.card := by exact_mod_cast card_pos.mpr hI
  have hXr : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  by_contra hn
  push_neg at hn
  let T : ℝ := ∑ i ∈ I, |∑ x ∈ X, G (b i) x*W i x|
  let A : ℝ := ∑ i ∈ I, |∑ x ∈ X, G false x*W i x|
  let B : ℝ := ∑ i ∈ I, |∑ x ∈ X, G true x*W i x|
  have hT : 0 ≤ T := sum_nonneg fun _ _ => abs_nonneg _
  have hAB : T ≤ A+B := by
    rw [show A+B=∑ i ∈ I, (|∑ x ∈ X, G false x*W i x|+|∑ x ∈ X, G true x*W i x|) by
      simp only [A,B,sum_add_distrib]]
    apply sum_le_sum
    intro i hi
    cases h : b i <;> linarith [abs_nonneg (∑ x ∈ X, G false x*W i x),
      abs_nonneg (∑ x ∈ X, G true x*W i x)]
  have hAsq := finite_bessel_absolute_sum I X (G false) W η hη (hG false) hW hGram
  have hBsq := finite_bessel_absolute_sum I X (G true) W η hη (hG true) hW hGram
  change A^2 ≤ _ at hAsq
  change B^2 ≤ _ at hBsq
  have hTsq : T^2 ≤ 4*(X.card : ℝ)^2*(I.card+(I.card : ℝ)^2*η) := by
    have hsq := pow_le_pow_left₀ hT hAB 2
    nlinarith [sq_nonneg (A-B)]
  have hlo : (I.card : ℝ)*ε*X.card ≤ T := by
    calc
      _ = ∑ _i ∈ I, ε*X.card := by simp; ring
      _ ≤ _ := sum_le_sum fun i hi => by
        have h := hn i hi
        rw [abs_div,abs_of_pos hXr] at h
        exact (le_div_iff₀ hXr).mp h
  have hloSq := pow_le_pow_left₀ (show 0 ≤ (I.card : ℝ)*ε*X.card by positivity) hlo 2
  have hmul := mul_lt_mul_of_pos_left hsize (show 0 < (I.card : ℝ)^2 by positivity)
  have he : (I.card : ℝ)^2*(4*((1 : ℝ)/I.card+η))=4*(I.card+(I.card : ℝ)^2*η) := by field_simp
  rw [he] at hmul
  have hmul' := mul_lt_mul_of_pos_left hmul (show 0 < (X.card : ℝ)^2 by positivity)
  nlinarith

#print axioms finite_bessel_two_target_selection
end Erdos371.FiniteSieve
