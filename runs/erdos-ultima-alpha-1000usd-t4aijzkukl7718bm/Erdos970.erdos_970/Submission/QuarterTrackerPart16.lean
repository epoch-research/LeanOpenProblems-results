import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_160 : run 100 ⟨2,6,7,3,16,4,10,6084309,993057280⟩ = ⟨0,1,8,8,1,6,12,6089829,993361024⟩ := by
  decide +kernel

lemma chunk_161 : run 100 ⟨0,1,8,8,1,6,12,6089829,993361024⟩ = ⟨1,3,9,13,9,6,13,6102565,993918080⟩ := by
  decide +kernel

lemma chunk_162 : run 100 ⟨1,3,9,13,9,6,13,6102565,993918080⟩ = ⟨2,5,10,18,17,9,15,6125221,995411072⟩ := by
  decide +kernel

lemma chunk_163 : run 100 ⟨2,5,10,18,17,9,15,6125221,995411072⟩ = ⟨0,0,0,4,2,6,11,6142469,997061760⟩ := by
  decide +kernel

lemma chunk_164 : run 100 ⟨0,0,0,4,2,6,11,6142469,997061760⟩ = ⟨1,2,1,9,10,6,12,6148005,997372288⟩ := by
  decide +kernel

lemma chunk_165 : run 100 ⟨1,2,1,9,10,6,12,6148005,997372288⟩ = ⟨2,4,2,14,18,7,14,6157125,998300032⟩ := by
  decide +kernel

lemma chunk_166 : run 100 ⟨2,4,2,14,18,7,14,6157125,998300032⟩ = ⟨0,6,3,0,3,9,14,6176773,1000577408⟩ := by
  decide +kernel

lemma chunk_167 : run 100 ⟨0,6,3,0,3,9,14,6176773,1000577408⟩ = ⟨1,1,4,5,11,8,16,6211077,1006295424⟩ := by
  decide +kernel

lemma chunk_168 : run 100 ⟨1,1,4,5,11,8,16,6211077,1006295424⟩ = ⟨2,3,5,10,19,8,14,6234181,1010026880⟩ := by
  decide +kernel

lemma chunk_169 : run 100 ⟨2,3,5,10,19,8,14,6234181,1010026880⟩ = ⟨0,5,6,15,4,6,16,6252421,1013459328⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
