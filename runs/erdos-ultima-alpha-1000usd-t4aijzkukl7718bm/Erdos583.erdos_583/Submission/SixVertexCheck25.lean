import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 25. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_100 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (100*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (100*256+l.val))) (certificate (100*256+l.val)) := by
  decide

lemma checked_101 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (101*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (101*256+l.val))) (certificate (101*256+l.val)) := by
  decide

lemma checked_102 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (102*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (102*256+l.val))) (certificate (102*256+l.val)) := by
  decide

lemma checked_103 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (103*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (103*256+l.val))) (certificate (103*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
