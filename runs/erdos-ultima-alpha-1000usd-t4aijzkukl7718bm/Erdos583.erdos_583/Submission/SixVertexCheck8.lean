import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 8. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_32 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (32*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (32*256+l.val))) (certificate (32*256+l.val)) := by
  decide

lemma checked_33 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (33*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (33*256+l.val))) (certificate (33*256+l.val)) := by
  decide

lemma checked_34 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (34*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (34*256+l.val))) (certificate (34*256+l.val)) := by
  decide

lemma checked_35 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (35*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (35*256+l.val))) (certificate (35*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
