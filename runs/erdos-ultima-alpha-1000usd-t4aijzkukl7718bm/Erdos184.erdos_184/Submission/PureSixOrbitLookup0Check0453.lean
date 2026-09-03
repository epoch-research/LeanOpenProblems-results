import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block453 : Table.Every Certificate block453 := by decide +kernel
lemma good_block453 : Table.Every GoodCertificate block453 := by decide +kernel
#print axioms certificate_block453
end Erdos184Work.PureSixOrbitLookup0
