import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 9. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_36 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (36*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (36*256+l.val))) (certificate (36*256+l.val)) := by
  decide

lemma checked_37 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (37*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (37*256+l.val))) (certificate (37*256+l.val)) := by
  decide

lemma checked_38 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (38*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (38*256+l.val))) (certificate (38*256+l.val)) := by
  decide

lemma checked_39 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (39*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (39*256+l.val))) (certificate (39*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
