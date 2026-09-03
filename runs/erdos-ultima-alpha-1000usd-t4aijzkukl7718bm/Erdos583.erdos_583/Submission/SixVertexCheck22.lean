import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 22. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_88 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (88*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (88*256+l.val))) (certificate (88*256+l.val)) := by
  decide

lemma checked_89 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (89*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (89*256+l.val))) (certificate (89*256+l.val)) := by
  decide

lemma checked_90 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (90*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (90*256+l.val))) (certificate (90*256+l.val)) := by
  decide

lemma checked_91 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (91*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (91*256+l.val))) (certificate (91*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
