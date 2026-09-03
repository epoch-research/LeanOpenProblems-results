import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 13. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_52 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (52*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (52*256+l.val))) (certificate (52*256+l.val)) := by
  decide

lemma checked_53 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (53*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (53*256+l.val))) (certificate (53*256+l.val)) := by
  decide

lemma checked_54 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (54*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (54*256+l.val))) (certificate (54*256+l.val)) := by
  decide

lemma checked_55 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (55*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (55*256+l.val))) (certificate (55*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
