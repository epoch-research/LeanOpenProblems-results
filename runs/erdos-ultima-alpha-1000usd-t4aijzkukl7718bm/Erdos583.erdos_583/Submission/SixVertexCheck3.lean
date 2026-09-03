import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 3. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_12 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (12*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (12*256+l.val))) (certificate (12*256+l.val)) := by
  decide

lemma checked_13 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (13*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (13*256+l.val))) (certificate (13*256+l.val)) := by
  decide

lemma checked_14 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (14*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (14*256+l.val))) (certificate (14*256+l.val)) := by
  decide

lemma checked_15 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (15*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (15*256+l.val))) (certificate (15*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
