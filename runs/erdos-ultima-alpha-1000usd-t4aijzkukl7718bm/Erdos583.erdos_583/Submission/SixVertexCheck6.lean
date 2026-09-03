import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 6. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_24 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (24*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (24*256+l.val))) (certificate (24*256+l.val)) := by
  decide

lemma checked_25 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (25*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (25*256+l.val))) (certificate (25*256+l.val)) := by
  decide

lemma checked_26 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (26*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (26*256+l.val))) (certificate (26*256+l.val)) := by
  decide

lemma checked_27 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (27*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (27*256+l.val))) (certificate (27*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
