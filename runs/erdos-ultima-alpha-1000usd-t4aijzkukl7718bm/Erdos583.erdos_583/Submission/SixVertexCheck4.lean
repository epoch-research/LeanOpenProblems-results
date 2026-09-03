import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 4. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_16 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (16*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (16*256+l.val))) (certificate (16*256+l.val)) := by
  decide

lemma checked_17 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (17*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (17*256+l.val))) (certificate (17*256+l.val)) := by
  decide

lemma checked_18 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (18*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (18*256+l.val))) (certificate (18*256+l.val)) := by
  decide

lemma checked_19 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (19*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (19*256+l.val))) (certificate (19*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
