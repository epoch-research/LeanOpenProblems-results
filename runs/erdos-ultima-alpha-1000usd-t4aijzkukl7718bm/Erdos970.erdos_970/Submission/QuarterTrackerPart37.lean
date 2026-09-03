import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_370 : run 100 ⟨2,6,8,8,17,9,17,10827713,1787264585⟩ = ⟨0,1,9,13,2,7,13,10867777,1792785993⟩ := by
  decide +kernel

lemma chunk_371 : run 100 ⟨0,1,9,13,2,7,13,10867777,1792785993⟩ = ⟨1,3,10,18,10,10,14,10919873,1794217545⟩ := by
  decide +kernel

lemma chunk_372 : run 100 ⟨1,3,10,18,10,10,14,10919873,1794217545⟩ = ⟨2,5,0,4,18,6,15,10953537,1795792457⟩ := by
  decide +kernel

lemma chunk_373 : run 100 ⟨2,5,0,4,18,6,15,10953537,1795792457⟩ = ⟨0,0,1,9,3,9,15,10972305,1797955145⟩ := by
  decide +kernel

lemma chunk_374 : run 100 ⟨0,0,1,9,3,9,15,10972305,1797955145⟩ = ⟨1,2,2,14,11,8,15,11024657,1802903113⟩ := by
  decide +kernel

lemma chunk_375 : run 100 ⟨1,2,2,14,11,8,15,11024657,1802903113⟩ = ⟨2,4,3,0,19,10,16,11076881,1809800777⟩ := by
  decide +kernel

lemma chunk_376 : run 100 ⟨2,4,3,0,19,10,16,11076881,1809800777⟩ = ⟨0,6,4,5,4,9,17,11204881,1815551561⟩ := by
  decide +kernel

lemma chunk_377 : run 100 ⟨0,6,4,5,4,9,17,11204881,1815551561⟩ = ⟨1,1,5,10,12,10,15,11287057,1820622409⟩ := by
  decide +kernel

lemma chunk_378 : run 100 ⟨1,1,5,10,12,10,15,11287057,1820622409⟩ = ⟨2,3,6,15,20,10,15,11762193,1825201737⟩ := by
  decide +kernel

lemma chunk_379 : run 100 ⟨2,3,6,15,20,10,15,11762193,1825201737⟩ = ⟨0,5,7,1,5,8,13,11856657,1827667529⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
