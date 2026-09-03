import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_20 : run 100 ⟨0,6,10,6,0,8,16,2416384,240970240⟩ = ⟨1,1,0,11,8,8,15,2431648,245135872⟩ := by
  decide +kernel

lemma chunk_21 : run 100 ⟨1,1,0,11,8,8,15,2431648,245135872⟩ = ⟨2,3,1,16,16,6,15,2451296,251132416⟩ := by
  decide +kernel

lemma chunk_22 : run 100 ⟨2,3,1,16,16,6,15,2451296,251132416⟩ = ⟨0,5,2,2,1,9,19,2522016,300415488⟩ := by
  decide +kernel

lemma chunk_23 : run 100 ⟨0,5,2,2,1,9,19,2522016,300415488⟩ = ⟨1,0,3,7,9,10,17,2618528,335673856⟩ := by
  decide +kernel

lemma chunk_24 : run 100 ⟨1,0,3,7,9,10,17,2618528,335673856⟩ = ⟨2,2,4,12,17,8,15,2653984,342129152⟩ := by
  decide +kernel

lemma chunk_25 : run 100 ⟨2,2,4,12,17,8,15,2653984,342129152⟩ = ⟨0,4,5,17,2,7,13,2705312,348092928⟩ := by
  decide +kernel

lemma chunk_26 : run 100 ⟨0,4,5,17,2,7,13,2705312,348092928⟩ = ⟨1,6,6,3,10,8,17,2732288,357480960⟩ := by
  decide +kernel

lemma chunk_27 : run 100 ⟨1,6,6,3,10,8,17,2732288,357480960⟩ = ⟨2,1,7,8,18,8,18,2808832,388479488⟩ := by
  decide +kernel

lemma chunk_28 : run 100 ⟨2,1,7,8,18,8,18,2808832,388479488⟩ = ⟨0,3,8,13,3,8,16,2844544,402577920⟩ := by
  decide +kernel

lemma chunk_29 : run 100 ⟨0,3,8,13,3,8,16,2844544,402577920⟩ = ⟨1,5,9,18,11,7,14,2888768,410155520⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
