import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 10. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_40 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (40*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (40*256+l.val))) (certificate (40*256+l.val)) := by
  decide

lemma checked_41 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (41*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (41*256+l.val))) (certificate (41*256+l.val)) := by
  decide

lemma checked_42 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (42*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (42*256+l.val))) (certificate (42*256+l.val)) := by
  decide

lemma checked_43 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (43*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (43*256+l.val))) (certificate (43*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
