import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_10 : run 100 ⟨2,0,0,13,12,9,17,1357504,47917568⟩ = ⟨0,2,1,18,20,11,20,1481920,91302400⟩ := by
  decide +kernel

lemma chunk_11 : run 100 ⟨0,2,1,18,20,11,20,1481920,91302400⟩ = ⟨1,4,2,4,5,10,16,1737408,114534912⟩ := by
  decide +kernel

lemma chunk_12 : run 100 ⟨1,4,2,4,5,10,16,1737408,114534912⟩ = ⟨2,6,3,9,13,9,16,1834176,126560768⟩ := by
  decide +kernel

lemma chunk_13 : run 100 ⟨2,6,3,9,13,9,16,1834176,126560768⟩ = ⟨0,1,4,14,21,10,16,2137792,191179264⟩ := by
  decide +kernel

lemma chunk_14 : run 100 ⟨0,1,4,14,21,10,16,2137792,191179264⟩ = ⟨1,3,5,0,6,8,17,2228672,198609408⟩ := by
  decide +kernel

lemma chunk_15 : run 100 ⟨1,3,5,0,6,8,17,2228672,198609408⟩ = ⟨2,5,6,5,14,9,16,2268608,204982784⟩ := by
  decide +kernel

lemma chunk_16 : run 100 ⟨2,5,6,5,14,9,16,2268608,204982784⟩ = ⟨0,0,7,10,22,8,14,2287968,208734720⟩ := by
  decide +kernel

lemma chunk_17 : run 100 ⟨0,0,7,10,22,8,14,2287968,208734720⟩ = ⟨1,2,8,15,7,9,17,2336608,222390784⟩ := by
  decide +kernel

lemma chunk_18 : run 100 ⟨1,2,8,15,7,9,17,2336608,222390784⟩ = ⟨2,4,9,1,15,6,16,2396896,234924544⟩ := by
  decide +kernel

lemma chunk_19 : run 100 ⟨2,4,9,1,15,6,16,2396896,234924544⟩ = ⟨0,6,10,6,0,8,16,2416384,240970240⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
