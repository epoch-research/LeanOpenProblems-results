import Submission.SieveInfiniteUniqueness

/-! A single-direction period test for the ordinary finite sieve.
The universal existence of a rejecting cutoff is not proved here. -/
namespace Erdos952Investigation.HorizontalPeriodCriterion
open FiniteSieveReduction PeriodicSieveComponents SieveInfiniteUniqueness
set_option maxHeartbeats 0

def horizontalPeriod (N : ℕ) : GaussianInt := ⟨N.factorial,0⟩

lemma horizontal_isPeriod (N : ℕ) : IsPeriod N (horizontalPeriod N) :=
  ⟨dvd_refl _,dvd_zero _⟩

lemma horizontal_ne_zero (N : ℕ) : horizontalPeriod N ≠ 0 := by
  intro h
  have hh := congrArg Zsqrtd.re h
  exact Nat.factorial_ne_zero N (Int.natCast_eq_zero.mp hh)

/-- Any one nonzero coordinate period detects an infinite component. -/
theorem sieve_ray_iff_horizontal_wrap (C : ℤ) (N : ℕ) :
    HasSieveRay C N ↔ ∃ z : GaussianInt,
      (sieveGraph C N).Reachable z (z+horizontalPeriod N) := by
  rw [sieve_ray_iff_infinite_component]
  exact exists_congr fun z => infinite_iff_reachable_given_period C N z _
    (horizontal_isPeriod N) (horizontal_ne_zero N)

/-- Periodicity reduces the starting vertices to a finite cell. -/
theorem sieve_ray_iff_cell_horizontal_wrap (C : ℤ) (N : ℕ) :
    HasSieveRay C N ↔ ∃ r : ZMod N.factorial × ZMod N.factorial,
      (sieveGraph C N).Reachable (representative N r)
        (representative N r+horizontalPeriod N) := by
  rw [sieve_ray_iff_horizontal_wrap]
  constructor
  · rintro ⟨z,hz⟩
    let w := representative N (residue N z)
    have hp : IsPeriod N (w-z) :=
      period_of_same_residue (residue_representative N (residue N z)).symm
    have ht := reachable_add_period hz hp
    have h0 : z+(w-z) = w := by abel
    have h1 : z+horizontalPeriod N+(w-z) = w+horizontalPeriod N := by abel
    rw [h0,h1] at ht
    exact ⟨residue N z,ht⟩
  · rintro ⟨r,hr⟩
    exact ⟨representative N r,hr⟩

/-- This is an exact criterion for failure of the stronger admissible-ray
condition. Its right side is not established for arbitrary `C`. -/
theorem no_admissible_ray_iff_horizontal_obstruction (C : ℤ) :
    (¬ HasAdmissibleRay C) ↔ ∃ N : ℕ,
      ∀ r : ZMod N.factorial × ZMod N.factorial,
        ¬ (sieveGraph C N).Reachable (representative N r)
          (representative N r+horizontalPeriod N) := by
  rw [admissible_ray_iff_finite_sieve_rays]
  simp only [sieve_ray_iff_cell_horizontal_wrap,not_forall,not_exists]

#print axioms no_admissible_ray_iff_horizontal_obstruction
end Erdos952Investigation.HorizontalPeriodCriterion
