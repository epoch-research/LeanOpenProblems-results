import Submission.OneHitCoreCorrelation
import Submission.AffinePhaseRescaling

/-! Exact translation of finite populations and their core completion weights.
The same phase equivalence is used for every point of the translated population. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

lemma add_phase_hit_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a x : ℕ) (r : Phase P) (p : P) :
    (a+x) % p.val = ((affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _) r) p).val ↔
      x % p.val = (r p).val := by
  rw [affinePhaseEquiv_val]
  simp only [one_mul]
  constructor
  · intro hh
    have he := Nat.ModEq.add_left_cancel' a hh
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (r p).isLt] using he
  · intro hh
    have he : x ≡ (r p).val [MOD p.val] := by
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt (r p).isLt] using hh
    exact he.add_left a

lemma populationSurvivors_image_add (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℕ) (r : Phase P) :
    populationSurvivors (S.image (fun x => a+x)) P
      (affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _) r) =
        (populationSurvivors S P r).image (fun x => a+x) := by
  ext y
  simp only [populationSurvivors,mem_filter,mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hh⟩
    refine ⟨x,⟨hx,?_⟩,rfl⟩
    intro p hp
    exact hh p ((add_phase_hit_iff P hP a x r p).mpr hp)
  · rintro ⟨x,⟨hx,hh⟩,rfl⟩
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    intro p hp
    exact hh p ((add_phase_hit_iff P hP a x r p).mp hp)

/-- Complete coverage probability is translation invariant, for any finite
population and without a one-hit assumption. -/
theorem populationCoveredFraction_image_add (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ) :
    populationCoveredFraction (S.image (fun x => a+x)) P = populationCoveredFraction S P := by
  unfold populationCoveredFraction
  simp_rw [← population_empty_iff]
  conv_lhs => rw [← phaseMean_equiv P
    (affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _))]
  simp only [populationSurvivors_image_add,Finset.image_eq_empty]

lemma coreCoverWeight_image_add (P R S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (a : ℕ) (r : Phase P) :
    coreCoverWeight P R (S.image (fun x => a+x))
      (affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _) r) = coreCoverWeight P R S r := by
  unfold coreCoverWeight
  rw [populationSurvivors_image_add,populationCoveredFraction_image_add R _ hR a]

/-- All scalar statistics of the core weights have the same translated mean.
This is not a factorization of joint statistics at two translates. -/
theorem coreCoverWeight_distribution_image_add (P R S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (a : ℕ) (F : ℝ → ℝ) :
    phaseMean P (fun r => F (coreCoverWeight P R (S.image (fun x => a+x)) r)) =
      phaseMean P (fun r => F (coreCoverWeight P R S r)) := by
  conv_lhs => rw [← phaseMean_equiv P
    (affinePhaseEquiv P hP a 1 (fun _ _ => Nat.coprime_one_left _))]
  simp only [coreCoverWeight_image_add P R S hP hR]

#print axioms populationCoveredFraction_image_add
#print axioms coreCoverWeight_distribution_image_add
end Erdos970.OneHitLogConcavity
