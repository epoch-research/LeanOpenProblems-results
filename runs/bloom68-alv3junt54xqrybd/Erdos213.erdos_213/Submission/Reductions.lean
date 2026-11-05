import Submission.DistanceScaling
import Submission.FiniteExamples

/-!
# Exact reductions for finite general-position distance configurations

These results do not assert arbitrary-size existence or a uniform bound.
They isolate those remaining assertions and prove their equivalences.
Neither admitted theorem in `Submission.Spec` is imported or used here.
-/

open EuclideanGeometry

namespace Erdos213Aux

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The rational-distance version of the finite existence predicate. -/
def RationalConfiguration (n : ℕ) : Prop :=
  ∃ S : Set Plane, S.Finite ∧ S.ncard = n ∧ NonTrilinear S ∧
    (∀ Q : Set Plane, Q ⊆ S ∧ Q.ncard = 4 → ¬ Cospherical Q) ∧
    (S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))

/-- For each fixed finite cardinality, clearing distance denominators is exact. -/
theorem integral_iff_rational (n : ℕ) :
    FiniteExamples.IntegralConfiguration n ↔ RationalConfiguration n := by
  constructor
  · rintro ⟨S, hfin, hcard, htri, hfour, hdist⟩
    refine ⟨S, hfin, hcard, htri, hfour, ?_⟩
    intro p hp q hq hpq
    obtain ⟨z, hz⟩ := hdist hp hq hpq
    refine ⟨(z : ℚ), ?_⟩
    simpa only [Rat.cast_intCast] using hz
  · rintro ⟨S, hfin, hcard, htri, hfour, hdist⟩
    obtain ⟨D, _, hscaledFin, hscaledCard, hscaledTri, hscaledFour, hscaledDist⟩ :=
      DistanceScaling.exists_integral_scaling_admissible hfin hdist htri hfour
    exact ⟨DistanceScaling.scale (D : ℝ) '' S, hscaledFin,
      hscaledCard.trans hcard, hscaledTri, hscaledFour, hscaledDist⟩

/-- All rational-distance existence conditions are downward closed too. -/
theorem RationalConfiguration.mono {m n : ℕ} (hm : RationalConfiguration m)
    (hnm : n ≤ m) : RationalConfiguration n :=
  (integral_iff_rational n).mp (((integral_iff_rational m).mpr hm).mono hnm)

/-- The verified seven-point construction supplies the rational cases as well. -/
theorem rationalConfiguration_of_le_seven (n : ℕ) (hn : n ≤ 7) :
    RationalConfiguration n :=
  (integral_iff_rational n).mp (FiniteExamples.integralConfiguration_of_le_seven n hn)

/-- Once the finite cases are accounted for, only cardinalities at least eight remain. -/
theorem universal_iff_from_eight :
    (∀ n : ℕ, 4 ≤ n → FiniteExamples.IntegralConfiguration n) ↔
      (∀ n : ℕ, 8 ≤ n → FiniteExamples.IntegralConfiguration n) := by
  constructor
  · intro h n hn
    exact h n (by omega)
  · intro h n _
    by_cases hn : 8 ≤ n
    · exact h n hn
    · exact FiniteExamples.integralConfiguration_of_le_seven n (by omega)

/-- Requiring cardinalities below four adds no further assertion. -/
theorem universal_iff_all_cardinalities :
    (∀ n : ℕ, 4 ≤ n → FiniteExamples.IntegralConfiguration n) ↔
      (∀ n : ℕ, FiniteExamples.IntegralConfiguration n) := by
  constructor
  · intro h n
    by_cases hn : 4 ≤ n
    · exact h n hn
    · exact FiniteExamples.integralConfiguration_of_le_seven n (by omega)
  · intro h n _
    exact h n

/-- A counterexample to the target assertion must occur at cardinality at least eight. -/
theorem not_universal_iff_counterexample_from_eight :
    (¬ ∀ n : ℕ, 4 ≤ n → FiniteExamples.IntegralConfiguration n) ↔
      ∃ n : ℕ, 8 ≤ n ∧ ¬ FiniteExamples.IntegralConfiguration n := by
  rw [universal_iff_from_eight]
  push_neg
  rfl

/-- In the negative direction, one obstruction and a uniform bound are equivalent. -/
theorem not_universal_iff_cardinalities_bounded :
    (¬ ∀ n : ℕ, 4 ≤ n → FiniteExamples.IntegralConfiguration n) ↔
      ∃ B : ℕ, ∀ n : ℕ, FiniteExamples.IntegralConfiguration n → n ≤ B := by
  constructor
  · intro h
    obtain ⟨N, _, hN⟩ := not_universal_iff_counterexample_from_eight.mp h
    refine ⟨N, ?_⟩
    intro n hn
    by_contra hle
    exact hN (hn.mono (by omega))
  · rintro ⟨B, hB⟩ h
    have hc := hB (B + 4) (h (B + 4) (by omega))
    omega

/-- No nesting of witnesses is assumed in the exact unbounded-cardinality reduction. -/
theorem universal_iff_unbounded_rational :
    (∀ n : ℕ, 4 ≤ n → FiniteExamples.IntegralConfiguration n) ↔
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ RationalConfiguration n) := by
  constructor
  · intro h N
    refine ⟨max N 4, le_max_left _ _, ?_⟩
    exact (integral_iff_rational _).mp (h _ (le_max_right _ _))
  · intro h n _
    obtain ⟨m, hnm, hm⟩ := h n
    exact ((integral_iff_rational m).mpr hm).mono hnm

/-- The unbounded-cardinality assertion can be stated directly on finite point sets. -/
theorem universal_iff_unbounded_rational_sets :
    (∀ n : ℕ, 4 ≤ n → FiniteExamples.IntegralConfiguration n) ↔
      (∀ N : ℕ, ∃ S : Set Plane, S.Finite ∧ N ≤ S.ncard ∧ NonTrilinear S ∧
        (∀ Q : Set Plane, Q ⊆ S ∧ Q.ncard = 4 → ¬ Cospherical Q) ∧
        (S.Pairwise fun p q => dist p q ∈ Set.range (Rat.cast : ℚ → ℝ))) := by
  rw [universal_iff_unbounded_rational]
  constructor
  · intro h N
    obtain ⟨n, hn, S, hfin, hcard, htri, hfour, hdist⟩ := h N
    exact ⟨S, hfin, by simpa only [hcard] using hn, htri, hfour, hdist⟩
  · intro h N
    obtain ⟨S, hfin, hcard, htri, hfour, hdist⟩ := h N
    exact ⟨S.ncard, hcard, S, hfin, rfl, htri, hfour, hdist⟩

#print axioms integral_iff_rational
#print axioms universal_iff_from_eight
#print axioms not_universal_iff_counterexample_from_eight
#print axioms not_universal_iff_cardinalities_bounded
#print axioms universal_iff_unbounded_rational_sets

end Erdos213Aux
