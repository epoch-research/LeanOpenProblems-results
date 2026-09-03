import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_400 : run 100 ⟨2,3,5,6,4,6,13,12610017,1932021833⟩ = ⟨0,5,6,11,12,7,15,12631521,1934426185⟩ := by
  decide +kernel

lemma chunk_401 : run 100 ⟨0,5,6,11,12,7,15,12631521,1934426185⟩ = ⟨1,0,7,16,20,9,16,12649121,1936658505⟩ := by
  decide +kernel

lemma chunk_402 : run 100 ⟨1,0,7,16,20,9,16,12649121,1936658505⟩ = ⟨2,2,8,2,5,9,16,12669793,1938546761⟩ := by
  decide +kernel

lemma chunk_403 : run 100 ⟨2,2,8,2,5,9,16,12669793,1938546761⟩ = ⟨0,4,9,7,13,6,13,12693025,1943126089⟩ := by
  decide +kernel

lemma chunk_404 : run 100 ⟨0,4,9,7,13,6,13,12693025,1943126089⟩ = ⟨1,6,10,12,21,8,15,12718561,1945448521⟩ := by
  decide +kernel

lemma chunk_405 : run 100 ⟨1,6,10,12,21,8,15,12718561,1945448521⟩ = ⟨2,1,0,17,6,10,20,12787361,1959940169⟩ := by
  decide +kernel

lemma chunk_406 : run 100 ⟨2,1,0,17,6,10,20,12787361,1959940169⟩ = ⟨0,3,1,3,14,8,13,12837409,1967534153⟩ := by
  decide +kernel

lemma chunk_407 : run 100 ⟨0,3,1,3,14,8,13,12837409,1967534153⟩ = ⟨1,5,2,8,22,5,13,12858753,1969242185⟩ := by
  decide +kernel

lemma chunk_408 : run 100 ⟨1,5,2,8,22,5,13,12858753,1969242185⟩ = ⟨2,0,3,13,7,6,13,12867809,1971531849⟩ := by
  decide +kernel

lemma chunk_409 : run 100 ⟨2,0,3,13,7,6,13,12867809,1971531849⟩ = ⟨0,2,4,18,15,7,16,12881409,1972987977⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
