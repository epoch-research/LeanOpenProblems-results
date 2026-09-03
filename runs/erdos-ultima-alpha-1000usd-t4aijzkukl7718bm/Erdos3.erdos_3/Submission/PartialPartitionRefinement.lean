import Submission.AveragedPartialPartitionIncrement

/-! Refining good cells of a partial partition. Exceptional masses add,
provided the inner exceptional bound is measured relative to each outer cell. -/
namespace Erdos3PartialPartitionRefinement
open Finset Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {V I J : Type*} [Fintype V] [Nonempty V] [Fintype I]

noncomputable def refineLabel (c : V → Option I) (b : I → V → Option J)
    (x : V) : Option (I × J) := (c x).bind (fun i ↦ (b i x).map (fun j ↦ (i,j)))

lemma refineLabel_some_iff (c : V → Option I) (b : I → V → Option J)
    (x : V) (i : I) (j : J) :
    refineLabel c b x = some (i,j) ↔ c x = some i ∧ b i x = some j := by
  simp [refineLabel,Option.bind_eq_some_iff,Option.map_eq_some_iff,Prod.mk.injEq]

/-- An inner exceptional proportion of at most tau in EVERY outer good cell
adds at most tau to the total exceptional mass. No bound on the number of
outer cells is needed. -/
theorem refineLabel_bad_mass (c : V → Option I) (b : I → V → Option J)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hbad : ∀ i, cellCharge c (fun x ↦ if b i x = none then 1 else 0) (some i) ≤
      τ*cellMass c (some i)) :
    cellMass (refineLabel c b) none ≤ cellMass c none+τ := by
  let g : V → ℝ := fun x ↦ if refineLabel c b x = none then 1 else 0
  have hnone : cellCharge c g none = cellMass c none := by
    unfold cellCharge cellMass
    apply expect_congr rfl
    intro x _
    by_cases hx : c x = none
    · simp [g,refineLabel,hx]
    · simp only [if_neg hx]
  have hsome (i : I) : cellCharge c g (some i) =
      cellCharge c (fun x ↦ if b i x = none then 1 else 0) (some i) := by
    unfold cellCharge
    apply expect_congr rfl
    intro x _
    by_cases hx : c x = some i
    · simp [g,refineLabel,hx]
    · simp only [if_neg hx]
  have hsum := sum_cellCharge c g
  rw [Fintype.sum_option,hnone] at hsum
  have he : (𝔼 x, g x) = cellMass (refineLabel c b) none := by
    unfold cellMass g
    apply expect_congr rfl
    intro x _
    split_ifs <;> rfl
  rw [he] at hsum
  have hm : (∑ i : I, cellMass c (some i)) ≤ 1 := by
    have hh := sum_cellMass c
    rw [Fintype.sum_option] at hh
    linarith [cellMass_nonneg c none]
  calc
    _ = cellMass c none+∑ i : I, cellCharge c g (some i) := hsum.symm
    _ ≤ cellMass c none+∑ i : I, τ*cellMass c (some i) := by
      apply add_le_add_right
      exact sum_le_sum (fun i _ ↦ (hsome i).le.trans (hbad i))
    _ = cellMass c none+τ*(∑ i : I, cellMass c (some i)) := by rw [mul_sum]
    _ ≤ cellMass c none+τ := add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hm hτ) _

#print axioms refineLabel_bad_mass
end Erdos3PartialPartitionRefinement
