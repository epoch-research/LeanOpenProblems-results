import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 7. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_28 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (28*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (28*256+l.val))) (certificate (28*256+l.val)) := by
  decide

lemma checked_29 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (29*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (29*256+l.val))) (certificate (29*256+l.val)) := by
  decide

lemma checked_30 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (30*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (30*256+l.val))) (certificate (30*256+l.val)) := by
  decide

lemma checked_31 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (31*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (31*256+l.val))) (certificate (31*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
