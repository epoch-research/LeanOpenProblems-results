import Submission.CompletionDisplacementBounds

/-! Relative versions of the signed one-prime displacement error. The
recursive child covariance is retained; these are not all-depth correlation
bounds or a settlement of the Jacobsthal conjecture. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 1500000

lemma populationConcentration_eq_insertion_gain (P S : Finset ℕ) (p : ℕ)
    (hp : 0 < p) (hpP : p ∉ P) :
    populationConcentration P S p = (p : ℝ)*
      (populationCoveredFraction S (insert p P)-populationCoveredFraction S P) := by
  have he := completionIncrement_mean_concentration P S p hp
  rw [completionIncrement_mean P S p hpP hp] at he
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  exact (div_eq_iff hpR).mp he.symm |>.trans (mul_comm _ _)

lemma concentration_product_eq_gain_product (P S T : Finset ℕ) (p : ℕ)
    (hp : 0 < p) (hpP : p ∉ P) :
    populationConcentration P S p*populationConcentration P T p/(p : ℝ) =
      (p : ℝ)*
        (populationCoveredFraction S (insert p P)-populationCoveredFraction S P)*
        (populationCoveredFraction T (insert p P)-populationCoveredFraction T P) := by
  rw [populationConcentration_eq_insertion_gain P S p hp hpP,
    populationConcentration_eq_insertion_gain P T p hp hpP]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- The concentration product is at the scale of the actual coverage
probabilities, rather than merely bounded by one. -/
lemma concentration_product_le_relative_cover (P S T : Finset ℕ) (p : ℕ)
    (hp : 0 < p) (hpP : p ∉ P) :
    populationConcentration P S p*populationConcentration P T p/(p : ℝ) ≤
      (p : ℝ)*populationCoveredFraction S (insert p P)*
        populationCoveredFraction T (insert p P) := by
  rw [concentration_product_eq_gain_product P S T p hp hpP]
  have hS := populationCoveredFraction_nonneg S P
  have hT := populationCoveredFraction_nonneg T P
  have hgainT : 0 ≤ populationCoveredFraction T (insert p P)-populationCoveredFraction T P := by
    rw [← completionIncrement_mean P T p hpP hp]
    exact residueMean_nonneg p (completionIncrement_nonneg P T p)
  have hh := mul_le_mul (sub_le_self _ hS) (sub_le_self _ hT) hgainT
    (populationCoveredFraction_nonneg S (insert p P))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg p)

/-- A short displacement sum of the signed source has a relative quadratic
bound. It does not include the recursively filtered child covariance. -/
theorem signedCompletionSource_displacement_relative (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (hpP : p ∉ P) (D : ℕ) :
    |∑ d ∈ range D, signedCompletionSource P S (T.image (fun x => d+x)) p| ≤
      (p : ℝ)*populationCoveredFraction S (insert p P)*
        populationCoveredFraction T (insert p P) :=
  (signedCompletionSource_displacement_sum_bound P S T hP p hp D).trans
    (concentration_product_le_relative_cover P S T p hp hpP)

/-- Exact averaged insertion, with a relative bound only on its error. -/
theorem averaged_coverageCovariance_insert_relative_error (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (hpP : p ∉ P) (D : ℕ) :
    |(∑ d ∈ range D, coverageCovariance (insert p P) S (T.image (fun x => d+x)))-
      (∑ d ∈ range D, residueMean p (fun a => coverageCovariance P
        (avoidClass S p a) (avoidClass (T.image (fun x => d+x)) p a)))| ≤
      (p : ℝ)*populationCoveredFraction S (insert p P)*
        populationCoveredFraction T (insert p P) :=
  (averaged_coverageCovariance_insert_error P S T hP p hp hpP D).trans
    (concentration_product_le_relative_cover P S T p hp hpP)

/-- For translated copies of one population, the normalized insertion error
is bounded by p/D times the square of its actual coverage probability.
The offset b can keep the two interval populations disjoint. -/
theorem averaged_translatedCovariance_insert_relative_error
    (P S : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) (b D : ℕ) :
    |((∑ d ∈ range D, coverageCovariance (insert p P) S
          ((S.image (fun x => b+x)).image (fun x => d+x)))-
       (∑ d ∈ range D, residueMean p (fun a => coverageCovariance P
         (avoidClass S p a)
         (avoidClass ((S.image (fun x => b+x)).image (fun x => d+x)) p a)))) /
       (D : ℝ)| ≤
      (p : ℝ)/(D : ℝ)*(populationCoveredFraction S (insert p P))^2 := by
  have hIns : ∀ q ∈ insert p P, q.Prime := by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hP q hq
  have hh := averaged_coverageCovariance_insert_relative_error P S
    (S.image (fun x => b+x)) hP p hp.pos hpP D
  rw [populationCoveredFraction_image_add (insert p P) S hIns b] at hh
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) D)]
  have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg D)
  convert hd using 1 <;> ring

#print axioms signedCompletionSource_displacement_relative
#print axioms averaged_coverageCovariance_insert_relative_error
#print axioms averaged_translatedCovariance_insert_relative_error
end Erdos970.OneHitLogConcavity
