import Submission.BestTransferRawData
/-! Explicit cycle partitions for the Best-edge raw-transfer obstruction. -/
open SimpleGraph
namespace Erdos184Work.BestTransferRaw
open Critical
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
def src0 : evenSource.Walk 0 0 :=
  .cons (show evenSource.Adj 0 1 by decide +kernel) (.cons (show evenSource.Adj 1 2 by decide +kernel) (.cons (show evenSource.Adj 2 0 by decide +kernel) (.nil)))
lemma src0_cycle : src0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def src1 : evenSource.Walk 1 1 :=
  .cons (show evenSource.Adj 1 3 by decide +kernel) (.cons (show evenSource.Adj 3 2 by decide +kernel) (.cons (show evenSource.Adj 2 4 by decide +kernel) (.cons (show evenSource.Adj 4 1 by decide +kernel) (.nil))))
lemma src1_cycle : src1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def src2 : evenSource.Walk 1 1 :=
  .cons (show evenSource.Adj 1 5 by decide +kernel) (.cons (show evenSource.Adj 5 2 by decide +kernel) (.cons (show evenSource.Adj 2 6 by decide +kernel) (.cons (show evenSource.Adj 6 1 by decide +kernel) (.nil))))
lemma src2_cycle : src2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def src3 : evenSource.Walk 3 3 :=
  .cons (show evenSource.Adj 3 7 by decide +kernel) (.cons (show evenSource.Adj 7 8 by decide +kernel) (.cons (show evenSource.Adj 8 3 by decide +kernel) (.nil)))
lemma src3_cycle : src3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def src4 : evenSource.Walk 7 7 :=
  .cons (show evenSource.Adj 7 9 by decide +kernel) (.cons (show evenSource.Adj 9 8 by decide +kernel) (.cons (show evenSource.Adj 8 10 by decide +kernel) (.cons (show evenSource.Adj 10 7 by decide +kernel) (.nil))))
lemma src4_cycle : src4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def src5 : evenSource.Walk 7 7 :=
  .cons (show evenSource.Adj 7 11 by decide +kernel) (.cons (show evenSource.Adj 11 8 by decide +kernel) (.cons (show evenSource.Adj 8 12 by decide +kernel) (.cons (show evenSource.Adj 12 7 by decide +kernel) (.nil))))
lemma src5_cycle : src5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def srcCycles : Fin 6 → Σ v : V, evenSource.Walk v v := ![⟨0,src0⟩,⟨1,src1⟩,⟨1,src2⟩,⟨3,src3⟩,⟨7,src4⟩,⟨7,src5⟩]
lemma evenSource_upper : number evenSource ≤ 6 := by
  apply DiminishingReturns.number_le_cycle_family (fun i => (srcCycles i).1) (fun i => (srcCycles i).2)
  · intro i
    fin_cases i
    · exact src0_cycle
    · exact src1_cycle
    · exact src2_cycle
    · exact src3_cycle
    · exact src4_cycle
    · exact src5_cycle
  · simp only [Finset.disjoint_left,List.mem_toFinset]
    decide +kernel
  · simp only [List.mem_toFinset]
    decide +kernel
def tgt0 : evenTarget.Walk 0 0 :=
  .cons (show evenTarget.Adj 0 1 by decide +kernel) (.cons (show evenTarget.Adj 1 2 by decide +kernel) (.cons (show evenTarget.Adj 2 3 by decide +kernel) (.cons (show evenTarget.Adj 3 7 by decide +kernel) (.cons (show evenTarget.Adj 7 8 by decide +kernel) (.cons (show evenTarget.Adj 8 0 by decide +kernel) (.nil))))))
lemma tgt0_cycle : tgt0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def tgt1 : evenTarget.Walk 0 0 :=
  .cons (show evenTarget.Adj 0 2 by decide +kernel) (.cons (show evenTarget.Adj 2 4 by decide +kernel) (.cons (show evenTarget.Adj 4 1 by decide +kernel) (.cons (show evenTarget.Adj 1 3 by decide +kernel) (.cons (show evenTarget.Adj 3 8 by decide +kernel) (.cons (show evenTarget.Adj 8 10 by decide +kernel) (.cons (show evenTarget.Adj 10 7 by decide +kernel) (.cons (show evenTarget.Adj 7 0 by decide +kernel) (.nil))))))))
lemma tgt1_cycle : tgt1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def tgt2 : evenTarget.Walk 1 1 :=
  .cons (show evenTarget.Adj 1 5 by decide +kernel) (.cons (show evenTarget.Adj 5 2 by decide +kernel) (.cons (show evenTarget.Adj 2 6 by decide +kernel) (.cons (show evenTarget.Adj 6 1 by decide +kernel) (.nil))))
lemma tgt2_cycle : tgt2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def tgt3 : evenTarget.Walk 7 7 :=
  .cons (show evenTarget.Adj 7 11 by decide +kernel) (.cons (show evenTarget.Adj 11 8 by decide +kernel) (.cons (show evenTarget.Adj 8 12 by decide +kernel) (.cons (show evenTarget.Adj 12 7 by decide +kernel) (.nil))))
lemma tgt3_cycle : tgt3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel
def tgtCycles : Fin 4 → Σ v : V, evenTarget.Walk v v := ![⟨0,tgt0⟩,⟨0,tgt1⟩,⟨1,tgt2⟩,⟨7,tgt3⟩]
lemma evenTarget_upper : number evenTarget ≤ 4 := by
  apply DiminishingReturns.number_le_cycle_family (fun i => (tgtCycles i).1) (fun i => (tgtCycles i).2)
  · intro i
    fin_cases i
    · exact tgt0_cycle
    · exact tgt1_cycle
    · exact tgt2_cycle
    · exact tgt3_cycle
  · simp only [Finset.disjoint_left,List.mem_toFinset]
    decide +kernel
  · simp only [List.mem_toFinset]
    decide +kernel
end Erdos184Work.BestTransferRaw
#print axioms Erdos184Work.BestTransferRaw.evenSource_upper
#print axioms Erdos184Work.BestTransferRaw.evenTarget_upper
