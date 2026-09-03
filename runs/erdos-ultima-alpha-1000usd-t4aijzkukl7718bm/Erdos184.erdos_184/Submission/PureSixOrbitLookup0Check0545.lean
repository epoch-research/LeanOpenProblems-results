import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block545 : Table.Every Certificate block545 := by decide +kernel
lemma good_block545 : Table.Every GoodCertificate block545 := by decide +kernel
#print axioms certificate_block545
end Erdos184Work.PureSixOrbitLookup0
