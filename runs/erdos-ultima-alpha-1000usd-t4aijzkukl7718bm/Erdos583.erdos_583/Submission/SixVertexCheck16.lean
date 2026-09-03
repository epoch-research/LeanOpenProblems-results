import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 16. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_64 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (64*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (64*256+l.val))) (certificate (64*256+l.val)) := by
  decide

lemma checked_65 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (65*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (65*256+l.val))) (certificate (65*256+l.val)) := by
  decide

lemma checked_66 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (66*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (66*256+l.val))) (certificate (66*256+l.val)) := by
  decide

lemma checked_67 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (67*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (67*256+l.val))) (certificate (67*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
