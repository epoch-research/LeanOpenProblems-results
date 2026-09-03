import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 30. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_120 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (120*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (120*256+l.val))) (certificate (120*256+l.val)) := by
  decide

lemma checked_121 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (121*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (121*256+l.val))) (certificate (121*256+l.val)) := by
  decide

lemma checked_122 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (122*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (122*256+l.val))) (certificate (122*256+l.val)) := by
  decide

lemma checked_123 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (123*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (123*256+l.val))) (certificate (123*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
