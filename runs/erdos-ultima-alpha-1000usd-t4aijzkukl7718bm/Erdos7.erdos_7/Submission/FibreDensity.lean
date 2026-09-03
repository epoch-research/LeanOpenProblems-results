import FormalConjecturesUtil

/-! Exact regional volume constraints for finite Cartesian-product covers.
These are necessary conditions, not a solution of Erdős Problem 7. -/

namespace Erdos7FibreDensity

/-- A box cover must have sufficient total intersection volume in every
Cartesian subregion, including a fibre with several coordinates fixed. -/
theorem region_card_le_sum_intersections {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ι → Type*} [DecidableEq ι] [∀ i, DecidableEq (A i)]
    (R : ∀ i, Finset (A i)) (B : κ → ∀ i, Finset (A i))
    (hc : ∀ x : ∀ i, A i, (∀ i, x i ∈ R i) → ∃ k, ∀ i, x i ∈ B k i) :
    (∏ i, (R i).card) ≤ ∑ k, ∏ i, ((R i) ∩ B k i).card := by
  classical
  let T (k : κ) := Fintype.piFinset (fun i => R i ∩ B k i)
  have hsub : Fintype.piFinset R ⊆ Finset.univ.biUnion T := by
    intro x hx
    obtain ⟨k, hk⟩ := hc x (Fintype.mem_piFinset.mp hx)
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ?_⟩
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_inter.mpr
      ⟨Fintype.mem_piFinset.mp hx i, hk i⟩)
  have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  simpa only [T, Fintype.card_piFinset] using h

/-- An exact strict volume deficit certifies an uncovered point without
enumerating all points of the Cartesian region. -/
theorem exists_uncovered_of_region_deficit {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ι → Type*} [DecidableEq ι] [∀ i, DecidableEq (A i)]
    (R : ∀ i, Finset (A i)) (B : κ → ∀ i, Finset (A i))
    (hdef : (∑ k, ∏ i, ((R i) ∩ B k i).card) < ∏ i, (R i).card) :
    ∃ x : ∀ i, A i, (∀ i, x i ∈ R i) ∧ ∀ k, ∃ i, x i ∉ B k i := by
  classical
  by_contra h
  push_neg at h
  have hc : ∀ x : ∀ i, A i, (∀ i, x i ∈ R i) → ∃ k, ∀ i, x i ∈ B k i := by
    intro x hx
    exact h x hx
  exact (not_lt_of_ge (region_card_le_sum_intersections R B hc)) hdef

#print axioms region_card_le_sum_intersections
#print axioms exists_uncovered_of_region_deficit
end Erdos7FibreDensity
