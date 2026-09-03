import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block762 : Table.Every Certificate block762 := by decide +kernel
lemma good_block762 : Table.Every GoodCertificate block762 := by decide +kernel
#print axioms certificate_block762
end Erdos184Work.PureSixOrbitLookup0
