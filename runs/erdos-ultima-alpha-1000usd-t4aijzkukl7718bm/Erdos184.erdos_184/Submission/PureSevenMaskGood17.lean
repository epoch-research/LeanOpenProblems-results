import Submission.PureSevenMasksBase
namespace Erdos184Work.PureSevenMasks
open FiniteCaseLookup
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma good_block17 : Table.Every GoodCertificate PureSixGoodLookup.block17 := by decide +kernel
#print axioms good_block17
end Erdos184Work.PureSevenMasks
