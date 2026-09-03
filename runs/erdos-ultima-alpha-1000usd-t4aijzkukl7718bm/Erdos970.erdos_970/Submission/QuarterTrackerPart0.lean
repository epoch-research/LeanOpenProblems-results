import Submission.QuarterTracker
/-! Short, independently kernel-checked state transitions. -/
namespace Erdos970.GapAverages.QuarterTracker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

lemma chunk_0 : run 100 ⟨1,1,1,1,1,15,15,0,0⟩ = ⟨2,3,2,6,9,7,11,459264,2492416⟩ := by
  decide +kernel

lemma chunk_1 : run 100 ⟨2,3,2,6,9,7,11,459264,2492416⟩ = ⟨0,5,3,11,17,8,13,493504,3316224⟩ := by
  decide +kernel

lemma chunk_2 : run 100 ⟨0,5,3,11,17,8,13,493504,3316224⟩ = ⟨1,0,4,16,2,10,16,550848,4680192⟩ := by
  decide +kernel

lemma chunk_3 : run 100 ⟨1,0,4,16,2,10,16,550848,4680192⟩ = ⟨2,2,5,2,10,11,15,609984,8063488⟩ := by
  decide +kernel

lemma chunk_4 : run 100 ⟨2,2,5,2,10,11,15,609984,8063488⟩ = ⟨0,4,6,7,18,10,14,778944,12192256⟩ := by
  decide +kernel

lemma chunk_5 : run 100 ⟨0,4,6,7,18,10,14,778944,12192256⟩ = ⟨1,6,7,12,3,8,14,920768,16050688⟩ := by
  decide +kernel

lemma chunk_6 : run 100 ⟨1,6,7,12,3,8,14,920768,16050688⟩ = ⟨2,1,8,17,11,11,18,1099968,21400064⟩ := by
  decide +kernel

lemma chunk_7 : run 100 ⟨2,1,8,17,11,11,18,1099968,21400064⟩ = ⟨0,3,9,3,19,11,16,1167808,25553408⟩ := by
  decide +kernel

lemma chunk_8 : run 100 ⟨0,3,9,3,19,11,16,1167808,25553408⟩ = ⟨1,5,10,8,4,10,15,1259456,38693376⟩ := by
  decide +kernel

lemma chunk_9 : run 100 ⟨1,5,10,8,4,10,15,1259456,38693376⟩ = ⟨2,0,0,13,12,9,17,1357504,47917568⟩ := by
  decide +kernel

end Erdos970.GapAverages.QuarterTracker
