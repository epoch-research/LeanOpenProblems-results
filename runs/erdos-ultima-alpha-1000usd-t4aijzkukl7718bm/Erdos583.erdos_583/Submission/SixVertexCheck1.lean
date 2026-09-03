import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 1. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_4 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (4*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (4*256+l.val))) (certificate (4*256+l.val)) := by
  decide

lemma checked_5 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (5*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (5*256+l.val))) (certificate (5*256+l.val)) := by
  decide

lemma checked_6 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (6*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (6*256+l.val))) (certificate (6*256+l.val)) := by
  decide

lemma checked_7 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (7*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (7*256+l.val))) (certificate (7*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
