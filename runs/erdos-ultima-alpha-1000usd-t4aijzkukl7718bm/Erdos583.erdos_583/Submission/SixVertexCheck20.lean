import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 20. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_80 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (80*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (80*256+l.val))) (certificate (80*256+l.val)) := by
  decide

lemma checked_81 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (81*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (81*256+l.val))) (certificate (81*256+l.val)) := by
  decide

lemma checked_82 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (82*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (82*256+l.val))) (certificate (82*256+l.val)) := by
  decide

lemma checked_83 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (83*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (83*256+l.val))) (certificate (83*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
