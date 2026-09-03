import Submission.ParityOneHitDyadic
import Submission.GapVarianceSubadditive

/-! Two-valued core counts permit an exact affine use of count covariance.
The one-hit/injectivity hypothesis on the remaining moduli is still required.
This does not give an unrestricted dyadic inequality. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

lemma phaseMean_centered_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f g : Phase P → ℝ) :
    phaseMean P (fun r => (f r-phaseMean P f)*(g r-phaseMean P g)) =
      phaseMean P (fun r => f r*g r)-phaseMean P f*phaseMean P g := by
  have he (r : Phase P) : (f r-phaseMean P f)*(g r-phaseMean P g) =
      f r*g r-phaseMean P g*f r-phaseMean P f*g r+phaseMean P f*phaseMean P g := by ring
  simp_rw [he]
  rw [phaseMean_add,phaseMean_sub,phaseMean_sub,phaseMean_mul,phaseMean_mul,
    phaseMean_const P hP]
  ring

lemma phaseMean_affine_covariance (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f g : Phase P → ℝ) (A B C D : ℝ) :
    phaseMean P (fun r => (A+B*f r)*(C+D*g r))-
      phaseMean P (fun r => A+B*f r)*phaseMean P (fun r => C+D*g r) =
    B*D*phaseMean P (fun r => (f r-phaseMean P f)*(g r-phaseMean P g)) := by
  rw [← phaseMean_centered_product P hP]
  simp only [phaseMean_add,phaseMean_mul,phaseMean_const P hP]
  have he (r : Phase P) :
      (A+B*f r-(A+B*phaseMean P f))*(C+D*g r-(C+D*phaseMean P g)) =
        (B*D)*((f r-phaseMean P f)*(g r-phaseMean P g)) := by ring
  simp_rw [he]
  exact phaseMean_mul P (B*D) _

lemma affine_adjacent_counts_nonpos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a m n : ℕ) (A B C D : ℝ) (hBD : 0 ≤ B*D) :
    phaseMean P (fun r => (A+B*blockCount P a m r)*(C+D*blockCount P (a+m) n r)) ≤
      phaseMean P (fun r => A+B*blockCount P a m r)*
        phaseMean P (fun r => C+D*blockCount P (a+m) n r) := by
  apply sub_nonpos.mp
  rw [phaseMean_affine_covariance P hP,phaseMean_block P hP,phaseMean_block P hP]
  exact mul_nonpos_of_nonneg_of_nonpos hBD (adjacent_count_covariance_nonpos P hP a m n)

lemma affine_of_two_values (F : ℕ → ℝ) (s c : ℕ) (hc : c = s ∨ c = s+1) :
    F c = (F s-(F (s+1)-F s)*(s : ℝ))+(F (s+1)-F s)*(c : ℝ) := by
  rcases hc with rfl | rfl <;> push_cast <;> ring

lemma populationSurvivors_card_translate (P : Finset ℕ) (a m : ℕ) (r : Phase P) :
    ((populationSurvivors ((range m).image (fun x => a+x)) P r).card : ℝ) =
      blockCount P a m r := by
  rw [populationSurvivors_card,Finset.sum_image]
  · rfl
  · intro x hx y hy hxy
    exact Nat.add_left_cancel hxy

/-- Every phase of every translate has the same two possible count values. -/
lemma two_valued_count_translate (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m s a : ℕ)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s ∨
      (populationSurvivors (range m) P r).card = s+1) (r : Phase P) :
    (populationSurvivors ((range m).image (fun x => a+x)) P r).card = s ∨
      (populationSurvivors ((range m).image (fun x => a+x)) P r).card = s+1 := by
  obtain ⟨r,rfl⟩ := (affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _)).surjective r
  rw [populationSurvivors_image_add,card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
  exact hc r

/-- The occupancy weight is genuinely affine on a two-point count range. -/
lemma balanced_core_weight_affine (P R : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hR : ∀ p ∈ R, p.Prime) (m s a : ℕ)
    (hlarge : ∀ p ∈ R, m ≤ p)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s ∨
      (populationSurvivors (range m) P r).card = s+1) (r : Phase P) :
    coreCoverWeight P R ((range m).image (fun x => a+x)) r =
      (occupancy R.toList s-(occupancy R.toList (s+1)-occupancy R.toList s)*(s : ℝ))+
        (occupancy R.toList (s+1)-occupancy R.toList s)*blockCount P a m r := by
  obtain ⟨r,rfl⟩ := (affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _)).surjective r
  rw [coreCoverWeight_image_add P R _ hP hR]
  rw [← populationSurvivors_card_translate,populationSurvivors_image_add,
    card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
  unfold coreCoverWeight
  have hS : populationSurvivors (range m) P r ⊆ range m := filter_subset _ _
  rw [population_eq_finset_occupancy R _ m (fun p hp => ⟨(hR p hp).pos,hlarge p hp⟩) hS]
  exact affine_of_two_values _ s _ (hc r)

/-- Nonpositive covariance of the actual completion weights, not an assumed
nonlinear extension of count covariance. Both counts have only two values. -/
theorem balanced_core_correlation_le (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hlarge : ∀ p ∈ R, m ≤ p)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s ∨
      (populationSurvivors (range m) P r).card = s+1) :
    phaseMean P (fun r => coreCoverWeight P R (range m) r*
      coreCoverWeight P R ((range m).image (fun x => m+x)) r) ≤
        coveredFraction (P ∪ R) m^2 := by
  let A := occupancy R.toList s-(occupancy R.toList (s+1)-occupancy R.toList s)*(s : ℝ)
  let B := occupancy R.toList (s+1)-occupancy R.toList s
  have he (a : ℕ) (r : Phase P) :
      coreCoverWeight P R ((range m).image (fun x => a+x)) r = A+B*blockCount P a m r :=
    balanced_core_weight_affine P R hP hR m s a hlarge hc r
  have he0 (r : Phase P) : coreCoverWeight P R (range m) r = A+B*blockCount P 0 m r := by
    simpa only [Nat.zero_add,image_id'] using he 0 r
  have hh := affine_adjacent_counts_nonpos P hP 0 m m A B A B (mul_self_nonneg B)
  simp only [Nat.zero_add,← he,image_id'] at hh
  rw [coreCoverWeight_mean P R _ hPR,coreCoverWeight_mean P R _ hPR] at hh
  have hU : ∀ p ∈ P ∪ R, p.Prime := fun p hp => (mem_union.mp hp).elim (hP p) (hR p)
  rw [populationCoveredFraction_image_add _ _ hU m,← void_eq_population] at hh
  simpa only [pow_two] using hh

/-- Loss-free dyadic doubling for a two-valued core and one-hit tail. -/
theorem balanced_void_double_le (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (hlarge : ∀ p ∈ R, 2*m ≤ p)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s ∨
      (populationSurvivors (range m) P r).card = s+1) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m^2 := by
  have hh := void_add_le_core_correlation P R m m hPR
    (fun p hp => ⟨(hR p hp).pos,by have := hlarge p hp; omega⟩)
  rw [← two_mul m] at hh
  exact hh.trans (balanced_core_correlation_le P R m s hP hR hPR
    (fun p hp => by have := hlarge p hp; omega) hc)

/-- Parity permits the same loss-free result with tail primes at least m. -/
theorem parity_balanced_void_double_le (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (h2 : 2 ∈ P) (hlarge : ∀ p ∈ R, m ≤ p)
    (hc : ∀ r : Phase P, (populationSurvivors (range m) P r).card = s ∨
      (populationSurvivors (range m) P r).card = s+1) :
    coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m^2 := by
  have hh := population_cover_le_core_correlation_add_collisions P R (range m)
    ((range m).image (fun x => m+x)) hPR hR (range_disjoint_translate m m)
  rw [← range_split_translate,← two_mul m,coreCollisionFraction_zero_of_parity P R m hR hPR h2 hlarge,
    add_zero,← void_eq_population] at hh
  exact hh.trans (balanced_core_correlation_le P R m s hP hR hPR hlarge hc)

#print axioms balanced_core_correlation_le
#print axioms balanced_void_double_le
#print axioms parity_balanced_void_double_le
end Erdos970.OneHitLogConcavity
