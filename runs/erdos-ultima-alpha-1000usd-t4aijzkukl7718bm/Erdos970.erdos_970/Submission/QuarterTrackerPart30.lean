import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_300 : run 100 ⟨1,6,4,0,9,8,14,9051785,1483864265⟩ = ⟨2,1,5,5,17,8,14,9076489,1484937417⟩ := by
  decide +kernel

lemma chunk_301 : run 100 ⟨2,1,5,5,17,8,14,9076489,1484937417⟩ = ⟨0,3,6,10,2,8,15,9094921,1488763081⟩ := by
  decide +kernel

lemma chunk_302 : run 100 ⟨0,3,6,10,2,8,15,9094921,1488763081⟩ = ⟨1,5,7,15,10,7,13,9118537,1491542217⟩ := by
  decide +kernel

lemma chunk_303 : run 100 ⟨1,5,7,15,10,7,13,9118537,1491542217⟩ = ⟨2,0,8,1,18,7,13,9142473,1492996297⟩ := by
  decide +kernel

lemma chunk_304 : run 100 ⟨2,0,8,1,18,7,13,9142473,1492996297⟩ = ⟨0,2,9,6,3,7,13,9156873,1493645513⟩ := by
  decide +kernel

lemma chunk_305 : run 100 ⟨0,2,9,6,3,7,13,9156873,1493645513⟩ = ⟨1,4,10,11,11,8,14,9166233,1494063561⟩ := by
  decide +kernel

lemma chunk_306 : run 100 ⟨1,4,10,11,11,8,14,9166233,1494063561⟩ = ⟨2,6,0,16,19,8,14,9203673,1495681481⟩ := by
  decide +kernel

lemma chunk_307 : run 100 ⟨2,6,0,16,19,8,14,9203673,1495681481⟩ = ⟨0,1,1,2,4,4,12,9214777,1496623561⟩ := by
  decide +kernel

lemma chunk_308 : run 100 ⟨0,1,1,2,4,4,12,9214777,1496623561⟩ = ⟨1,3,2,7,12,6,13,9222633,1497219017⟩ := by
  decide +kernel

lemma chunk_309 : run 100 ⟨1,3,2,7,12,6,13,9222633,1497219017⟩ = ⟨2,5,3,12,20,6,14,9236617,1498521545⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
