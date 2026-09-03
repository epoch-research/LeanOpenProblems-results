import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block677 : Table.Every Certificate block677 := by decide +kernel
lemma good_block677 : Table.Every GoodCertificate block677 := by decide +kernel
#print axioms certificate_block677
end Erdos184Work.PureSixOrbitLookup0
