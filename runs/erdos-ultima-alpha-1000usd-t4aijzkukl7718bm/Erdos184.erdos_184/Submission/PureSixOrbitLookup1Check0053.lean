import Submission.PureSixOrbitLookup1CertificateBase
namespace Erdos184Work.PureSixOrbitLookup1
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block53 : Table.Every Certificate block53 := by decide +kernel
#print axioms certificate_block53
end Erdos184Work.PureSixOrbitLookup1
