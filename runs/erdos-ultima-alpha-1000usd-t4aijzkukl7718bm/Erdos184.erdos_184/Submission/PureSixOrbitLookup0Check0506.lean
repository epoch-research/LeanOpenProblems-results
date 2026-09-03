import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block506 : Table.Every Certificate block506 := by decide +kernel
lemma good_block506 : Table.Every GoodCertificate block506 := by decide +kernel
#print axioms certificate_block506
end Erdos184Work.PureSixOrbitLookup0
