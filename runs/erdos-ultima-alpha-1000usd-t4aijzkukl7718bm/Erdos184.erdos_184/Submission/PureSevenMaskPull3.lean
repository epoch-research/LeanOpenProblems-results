import Submission.PureSevenMasksBase
namespace Erdos184Work.PureSevenMasks
open PureSevenProjectionNumbers
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma pull_valid3 : ∀ (m : Masks) (q : Fin 60),
    (pull3 m).testBit q.val = (smallMask m).testBit (enc3_5 q).val := by decide +kernel
#print axioms pull_valid3
end Erdos184Work.PureSevenMasks
