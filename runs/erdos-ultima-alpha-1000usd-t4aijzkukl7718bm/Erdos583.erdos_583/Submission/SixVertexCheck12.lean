import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 12. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_48 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (48*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (48*256+l.val))) (certificate (48*256+l.val)) := by
  decide

lemma checked_49 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (49*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (49*256+l.val))) (certificate (49*256+l.val)) := by
  decide

lemma checked_50 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (50*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (50*256+l.val))) (certificate (50*256+l.val)) := by
  decide

lemma checked_51 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (51*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (51*256+l.val))) (certificate (51*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
