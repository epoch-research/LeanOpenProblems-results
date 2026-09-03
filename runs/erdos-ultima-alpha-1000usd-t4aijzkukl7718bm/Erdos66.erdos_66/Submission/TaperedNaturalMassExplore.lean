import Submission.TaperedRowAverageExplore
import Submission.PhasedResidueCountingExplore

/-! The row first moment also gives an exact average of ordinary natural
prefix cardinalities. It is not a representation-count conclusion. -/
namespace Erdos66TaperedNaturalMass
open Erdos66TaperedFaithfulLift Erdos66TaperedRowAverage
  Erdos66IntegerBlock Erdos66Counting Erdos66PhasedResidueCounting
open scoped Classical
variable {p : ℕ} [Fact p.Prime]

noncomputable def safeNaturalSet (U : ℕ → Finset (ZMod p)) (a : ZMod p) : Set ℕ :=
  blockSet p (fun k ↦ safeRow (U k) a (k:ZMod p))

/-- All rows, cutoff positions, and parameter sets are chosen before taking
the average. The identity itself places no nesting requirement on them. -/
theorem prefix_mass_translation_sum (U : ℕ → Finset (ZMod p)) (N : ℕ) :
    (∑ a : ZMod p, count (safeNaturalSet U a) (N*p))=
      ∑ k∈Finset.range N, (U k).card*(p-if (k:ZMod p)=0 then 1 else 2) := by
  simp only [safeNaturalSet,count_blocks]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [ZMod.card] using safeRow_translation_average (U k) (k:ZMod p)

end Erdos66TaperedNaturalMass
