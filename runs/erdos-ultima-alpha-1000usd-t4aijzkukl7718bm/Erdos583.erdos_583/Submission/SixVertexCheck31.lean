import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 31. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_124 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (124*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (124*256+l.val))) (certificate (124*256+l.val)) := by
  decide

lemma checked_125 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (125*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (125*256+l.val))) (certificate (125*256+l.val)) := by
  decide

lemma checked_126 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (126*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (126*256+l.val))) (certificate (126*256+l.val)) := by
  decide

lemma checked_127 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (127*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (127*256+l.val))) (certificate (127*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
