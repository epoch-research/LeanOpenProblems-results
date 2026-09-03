import Submission.RestrictedPartialPartition

/-! Exact conditional-mass transfer when a retained coarse progression fiber
is refined in its natural local coordinate. -/
namespace Erdos3RestrictedProgressionRefinement
open Finset Erdos3RestrictedPartialPartition Erdos3ProgressionFiberEquivalence
  Erdos3IntervalProgressionPartition Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- Refinement of a retained complete progression preserves its conditional
exceptional mass exactly. This is the link needed to refine Bohr-domain coarse
partitions using the local quadratic progression partition. -/
lemma restricted_progression_inner_bad_charge {N d M : ℕ} {J : Type*}
    (hd : 0 < d) (hM : 0 < M) (B : Finset (Fin N)) (a : Fin N)
    (ha : (cell (progressionLabel N d M) (some a)).Nonempty)
    (hfull : cell (progressionLabel N d M) (some a) ⊆ B) (b : Fin M → Option J) :
    cellCharge (restrictLabel B (progressionLabel N d M))
      (fun x ↦ if b ⟨x.val.val/d%M,Nat.mod_lt _ hM⟩ = none then 1 else 0) (some a) =
      cellMass (restrictLabel B (progressionLabel N d M)) (some a)*cellMass b none := by
  let e := (progressionFiberEquiv hd hM a ha).trans
    (restrictFiberEquiv B (progressionLabel N d M) a hfull)
  have hc : (cell (restrictLabel B (progressionLabel N d M)) (some a)).Nonempty := by
    let x := e ⟨0,hM⟩
    exact ⟨x.val,x.property⟩
  letI : Nonempty B := ⟨hc.choose⟩
  rw [cellCharge_eq_mean _ _ _ hc]
  congr 1
  unfold cellMass
  apply (Fintype.expect_equiv e _ _ ?_).symm
  intro j
  have he : (⟨(e j).val.val.val/d%M,Nat.mod_lt _ hM⟩ : Fin M) = j := by
    apply Fin.ext
    exact progressionLabel_coordinate hd hM a ha j.isLt
  rw [he]
  split_ifs <;> rfl

#print axioms restricted_progression_inner_bad_charge
end Erdos3RestrictedProgressionRefinement
