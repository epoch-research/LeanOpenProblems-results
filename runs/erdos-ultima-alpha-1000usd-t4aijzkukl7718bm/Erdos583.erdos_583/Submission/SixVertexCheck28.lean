import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 28. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_112 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (112*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (112*256+l.val))) (certificate (112*256+l.val)) := by
  decide

lemma checked_113 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (113*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (113*256+l.val))) (certificate (113*256+l.val)) := by
  decide

lemma checked_114 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (114*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (114*256+l.val))) (certificate (114*256+l.val)) := by
  decide

lemma checked_115 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (115*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (115*256+l.val))) (certificate (115*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
