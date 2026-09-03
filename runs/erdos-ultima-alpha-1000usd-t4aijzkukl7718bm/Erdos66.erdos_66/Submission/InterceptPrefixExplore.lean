import Submission.InterceptUpperAndMassExplore
import Submission.PrefixFaithfulParabolaLiftExplore

/-! Literal row-zero and natural-prefix preservation for the intercept
curves. The collision correction remains necessary for set-level counts. -/
namespace Erdos66InterceptPrefix
open Erdos66InterceptCurve Erdos66InterceptUpperAndMass
  Erdos66PrefixFaithfulParabolaLift Erdos66InheritedOriginLift
  Erdos66OriginRepair Erdos66ShearedParabolaPrefix
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1600000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def anchored (U : Finset F) (a : F) : Finset (F × F) :=
  shiftSet (curveUnion (translated U a)) (-a,0)

lemma anchored_row_zero (U : Finset F) (a x : F) :
    (x,0)∈anchored U a ↔ x∈U := by
  rw [anchored,mem_shiftSet]
  have he : (x,(0 : F))-(-a,0)=(x+a,0) := by ext <;> simp
  rw [he,curveUnion_row_zero]
  change x+a∈shiftSet U a ↔ x∈U
  rw [mem_shiftSet,add_sub_cancel_right]

lemma anchored_pairCount (U : Finset F) (a : F) (z : F × F) :
    pairCount (anchored U a) (anchored U a) z=
      pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) (z-(-a,0)-(-a,0)) := by
  exact pairCount_shiftSet _ _ _ _ _

lemma encoded_prefix (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (a : ZMod p) (n : ℕ) (hn : n<p) :
    n∈encodePlane p (anchored U a) ↔ (n : ZMod p)∈U := by
  rw [encodePlane_prefix p _ n hn,anchored_row_zero]

lemma encoded_counts_below (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (a : ZMod p) (n : ℕ) (hn : n<p) :
    sumRep (encodePlane p (anchored U a) : Set ℕ) n=
      sumRep {k : ℕ | k<p ∧ (k : ZMod p)∈U} n := by
  apply Erdos66Compactness.sumRep_congr_below
  intro k hk
  have hkp : k<p := lt_of_le_of_lt hk hn
  simpa only [Finset.mem_coe,Set.mem_setOf_eq,hkp,true_and] using encoded_prefix p U a k hkp

end Erdos66InterceptPrefix
