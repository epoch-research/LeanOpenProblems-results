import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_130 : run 100 ⟨2,2,10,5,6,7,15,5421197,864850688⟩ = ⟨0,4,0,10,14,6,14,5432269,869577472⟩ := by
  decide +kernel

lemma chunk_131 : run 100 ⟨0,4,0,10,14,6,14,5432269,869577472⟩ = ⟨1,6,1,15,22,7,15,5452877,871756544⟩ := by
  decide +kernel

lemma chunk_132 : run 100 ⟨1,6,1,15,22,7,15,5452877,871756544⟩ = ⟨2,1,2,1,7,4,13,5456853,872968960⟩ := by
  decide +kernel

lemma chunk_133 : run 100 ⟨2,1,2,1,7,4,13,5456853,872968960⟩ = ⟨0,3,3,6,15,9,16,5463845,874697472⟩ := by
  decide +kernel

lemma chunk_134 : run 100 ⟨0,3,3,6,15,9,16,5463845,874697472⟩ = ⟨1,5,4,11,0,7,14,5480997,880767744⟩ := by
  decide +kernel

lemma chunk_135 : run 100 ⟨1,5,4,11,0,7,14,5480997,880767744⟩ = ⟨2,0,5,16,8,10,16,5507813,885052160⟩ := by
  decide +kernel

lemma chunk_136 : run 100 ⟨2,0,5,16,8,10,16,5507813,885052160⟩ = ⟨0,2,6,2,16,7,14,5528101,887255808⟩ := by
  decide +kernel

lemma chunk_137 : run 100 ⟨0,2,6,2,16,7,14,5528101,887255808⟩ = ⟨1,4,7,7,1,9,15,5543685,890061568⟩ := by
  decide +kernel

lemma chunk_138 : run 100 ⟨1,4,7,7,1,9,15,5543685,890061568⟩ = ⟨2,6,8,12,9,6,15,5565189,895607552⟩ := by
  decide +kernel

lemma chunk_139 : run 100 ⟨2,6,8,12,9,6,15,5565189,895607552⟩ = ⟨0,1,9,17,17,7,16,5592773,898667264⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
