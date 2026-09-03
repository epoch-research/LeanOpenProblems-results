import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_120 : run 100 ⟨1,3,0,12,18,7,16,5349376,823918848⟩ = ⟨2,5,1,17,3,7,13,5360736,825543424⟩ := by
  decide +kernel

lemma chunk_121 : run 100 ⟨2,5,1,17,3,7,13,5360736,825543424⟩ = ⟨0,0,2,3,11,6,13,5369168,827939584⟩ := by
  decide +kernel

lemma chunk_122 : run 100 ⟨0,0,2,3,11,6,13,5369168,827939584⟩ = ⟨1,2,3,8,19,4,12,5375392,831294208⟩ := by
  decide +kernel

lemma chunk_123 : run 100 ⟨1,2,3,8,19,4,12,5375392,831294208⟩ = ⟨2,4,4,13,4,5,15,5379928,834013952⟩ := by
  decide +kernel

lemma chunk_124 : run 100 ⟨2,4,4,13,4,5,15,5379928,834013952⟩ = ⟨0,6,5,18,12,5,15,5385472,839799552⟩ := by
  decide +kernel

lemma chunk_125 : run 100 ⟨0,6,5,18,12,5,15,5385472,839799552⟩ = ⟨1,1,6,4,20,3,14,5387728,842461952⟩ := by
  decide +kernel

lemma chunk_126 : run 100 ⟨1,1,6,4,20,3,14,5387728,842461952⟩ = ⟨2,3,7,9,5,5,13,5390141,847377152⟩ := by
  decide +kernel

lemma chunk_127 : run 100 ⟨2,3,7,9,5,5,13,5390141,847377152⟩ = ⟨0,5,8,14,13,5,16,5399885,853938944⟩ := by
  decide +kernel

lemma chunk_128 : run 100 ⟨0,5,8,14,13,5,16,5399885,853938944⟩ = ⟨1,0,9,0,21,8,17,5405965,859198208⟩ := by
  decide +kernel

lemma chunk_129 : run 100 ⟨1,0,9,0,21,8,17,5405965,859198208⟩ = ⟨2,2,10,5,6,7,15,5421197,864850688⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
