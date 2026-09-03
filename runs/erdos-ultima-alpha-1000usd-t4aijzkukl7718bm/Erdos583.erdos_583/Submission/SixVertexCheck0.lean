import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 0. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_0 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (0*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (0*256+l.val))) (certificate (0*256+l.val)) := by
  decide

lemma checked_1 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (1*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (1*256+l.val))) (certificate (1*256+l.val)) := by
  decide

lemma checked_2 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (2*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (2*256+l.val))) (certificate (2*256+l.val)) := by
  decide

lemma checked_3 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (3*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (3*256+l.val))) (certificate (3*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
