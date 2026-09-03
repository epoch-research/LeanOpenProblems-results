import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 14. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_56 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (56*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (56*256+l.val))) (certificate (56*256+l.val)) := by
  decide

lemma checked_57 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (57*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (57*256+l.val))) (certificate (57*256+l.val)) := by
  decide

lemma checked_58 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (58*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (58*256+l.val))) (certificate (58*256+l.val)) := by
  decide

lemma checked_59 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (59*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (59*256+l.val))) (certificate (59*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
