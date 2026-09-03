import Submission.PureSixOrbitLookup0CertificateBase
namespace Erdos184Work.PureSixOrbitLookup0
open FiniteCaseLookup
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma certificate_block447 : Table.Every Certificate block447 := by decide +kernel
lemma good_block447 : Table.Every GoodCertificate block447 := by decide +kernel
#print axioms certificate_block447
end Erdos184Work.PureSixOrbitLookup0
