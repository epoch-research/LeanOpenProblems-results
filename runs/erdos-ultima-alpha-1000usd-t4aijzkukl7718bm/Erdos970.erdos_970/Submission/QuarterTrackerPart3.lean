import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_30 : run 100 ⟨1,5,9,18,11,7,14,2888768,410155520⟩ = ⟨2,0,10,4,19,9,16,2926976,412805632⟩ := by
  decide +kernel

lemma chunk_31 : run 100 ⟨2,0,10,4,19,9,16,2926976,412805632⟩ = ⟨0,2,0,9,4,7,14,2956544,416754176⟩ := by
  decide +kernel

lemma chunk_32 : run 100 ⟨0,2,0,9,4,7,14,2956544,416754176⟩ = ⟨1,4,1,14,12,7,12,2966464,418180096⟩ := by
  decide +kernel

lemma chunk_33 : run 100 ⟨1,4,1,14,12,7,12,2966464,418180096⟩ = ⟨2,6,2,0,20,8,17,2990720,420686848⟩ := by
  decide +kernel

lemma chunk_34 : run 100 ⟨2,6,2,0,20,8,17,2990720,420686848⟩ = ⟨0,1,3,5,5,6,14,3000640,424856576⟩ := by
  decide +kernel

lemma chunk_35 : run 100 ⟨0,1,3,5,5,6,14,3000640,424856576⟩ = ⟨1,3,4,10,13,9,17,3034368,431102976⟩ := by
  decide +kernel

lemma chunk_36 : run 100 ⟨1,3,4,10,13,9,17,3034368,431102976⟩ = ⟨2,5,5,15,21,9,15,3062016,445180928⟩ := by
  decide +kernel

lemma chunk_37 : run 100 ⟨2,5,5,15,21,9,15,3062016,445180928⟩ = ⟨0,0,6,1,6,9,14,3105408,449154048⟩ := by
  decide +kernel

lemma chunk_38 : run 100 ⟨0,0,6,1,6,9,14,3105408,449154048⟩ = ⟨1,2,7,6,14,7,14,3129376,454364160⟩ := by
  decide +kernel

lemma chunk_39 : run 100 ⟨1,2,7,6,14,7,14,3129376,454364160⟩ = ⟨2,4,8,11,22,8,13,3142624,455287296⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
