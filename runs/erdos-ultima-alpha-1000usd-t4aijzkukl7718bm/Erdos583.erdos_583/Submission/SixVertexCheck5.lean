import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 5. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_20 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (20*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (20*256+l.val))) (certificate (20*256+l.val)) := by
  decide

lemma checked_21 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (21*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (21*256+l.val))) (certificate (21*256+l.val)) := by
  decide

lemma checked_22 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (22*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (22*256+l.val))) (certificate (22*256+l.val)) := by
  decide

lemma checked_23 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (23*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (23*256+l.val))) (certificate (23*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
