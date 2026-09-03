import Submission.PureSixOrbitLookup2CertificateBase
namespace Erdos184Work.PureSixOrbitLookup2
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block0 : Table.Every Certificate block0 := by decide +kernel
#print axioms certificate_block0
end Erdos184Work.PureSixOrbitLookup2
