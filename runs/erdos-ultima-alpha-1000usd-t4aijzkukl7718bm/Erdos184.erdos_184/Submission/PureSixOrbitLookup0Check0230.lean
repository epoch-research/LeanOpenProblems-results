import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block230 : Table.Every Certificate block230 := by decide +kernel
lemma good_block230 : Table.Every GoodCertificate block230 := by decide +kernel
#print axioms certificate_block230
end Erdos184Work.PureSixOrbitLookup0
