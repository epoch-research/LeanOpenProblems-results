import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_40 : run 100 ⟨2,4,8,11,22,8,13,3142624,455287296⟩ = ⟨0,6,9,16,7,8,17,3156672,456905216⟩ := by
  decide +kernel

lemma chunk_41 : run 100 ⟨0,6,9,16,7,8,17,3156672,456905216⟩ = ⟨1,1,10,2,15,7,15,3166528,459575808⟩ := by
  decide +kernel

lemma chunk_42 : run 100 ⟨1,1,10,2,15,7,15,3166528,459575808⟩ = ⟨2,3,0,7,0,8,16,3192128,465416704⟩ := by
  decide +kernel

lemma chunk_43 : run 100 ⟨2,3,0,7,0,8,16,3192128,465416704⟩ = ⟨0,5,1,12,8,9,16,3310016,470561280⟩ := by
  decide +kernel

lemma chunk_44 : run 100 ⟨0,5,1,12,8,9,16,3310016,470561280⟩ = ⟨1,0,2,17,16,7,15,3335808,473014784⟩ := by
  decide +kernel

lemma chunk_45 : run 100 ⟨1,0,2,17,16,7,15,3335808,473014784⟩ = ⟨2,2,3,3,1,7,14,3353792,477729280⟩ := by
  decide +kernel

lemma chunk_46 : run 100 ⟨2,2,3,3,1,7,14,3353792,477729280⟩ = ⟨0,4,4,8,9,7,16,3369072,485249536⟩ := by
  decide +kernel

lemma chunk_47 : run 100 ⟨0,4,4,8,9,7,16,3369072,485249536⟩ = ⟨1,6,5,13,17,7,17,3388144,492483072⟩ := by
  decide +kernel

lemma chunk_48 : run 100 ⟨1,6,5,13,17,7,17,3388144,492483072⟩ = ⟨2,1,6,18,2,7,15,3431920,501305856⟩ := by
  decide +kernel

lemma chunk_49 : run 100 ⟨2,1,6,18,2,7,15,3431920,501305856⟩ = ⟨0,3,7,4,10,7,15,3454064,504726016⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
