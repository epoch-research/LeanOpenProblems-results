import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 24. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_96 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (96*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (96*256+l.val))) (certificate (96*256+l.val)) := by
  decide

lemma checked_97 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (97*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (97*256+l.val))) (certificate (97*256+l.val)) := by
  decide

lemma checked_98 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (98*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (98*256+l.val))) (certificate (98*256+l.val)) := by
  decide

lemma checked_99 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (99*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (99*256+l.val))) (certificate (99*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
