import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 2. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_8 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (8*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (8*256+l.val))) (certificate (8*256+l.val)) := by
  decide

lemma checked_9 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (9*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (9*256+l.val))) (certificate (9*256+l.val)) := by
  decide

lemma checked_10 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (10*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (10*256+l.val))) (certificate (10*256+l.val)) := by
  decide

lemma checked_11 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (11*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (11*256+l.val))) (certificate (11*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
