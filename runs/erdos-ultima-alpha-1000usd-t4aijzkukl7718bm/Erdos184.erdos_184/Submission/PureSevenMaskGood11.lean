import Submission.PureSevenMasksBase
namespace Erdos184Work.PureSevenMasks
open FiniteCaseLookup
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma good_block11 : Table.Every GoodCertificate PureSixGoodLookup.block11 := by decide +kernel
#print axioms good_block11
end Erdos184Work.PureSevenMasks
