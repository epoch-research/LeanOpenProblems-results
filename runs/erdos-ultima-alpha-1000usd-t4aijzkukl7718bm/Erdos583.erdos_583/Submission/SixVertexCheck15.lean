import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 15. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_60 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (60*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (60*256+l.val))) (certificate (60*256+l.val)) := by
  decide

lemma checked_61 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (61*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (61*256+l.val))) (certificate (61*256+l.val)) := by
  decide

lemma checked_62 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (62*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (62*256+l.val))) (certificate (62*256+l.val)) := by
  decide

lemma checked_63 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (63*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (63*256+l.val))) (certificate (63*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
