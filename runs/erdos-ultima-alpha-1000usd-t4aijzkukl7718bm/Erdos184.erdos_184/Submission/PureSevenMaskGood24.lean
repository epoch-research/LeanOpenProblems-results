import Submission.PureSevenMasksBase
namespace Erdos184Work.PureSevenMasks
open FiniteCaseLookup
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma good_block24 : Table.Every GoodCertificate PureSixGoodLookup.block24 := by decide +kernel
#print axioms good_block24
end Erdos184Work.PureSevenMasks
