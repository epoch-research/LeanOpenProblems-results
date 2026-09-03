import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 23. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_92 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (92*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (92*256+l.val))) (certificate (92*256+l.val)) := by
  decide

lemma checked_93 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (93*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (93*256+l.val))) (certificate (93*256+l.val)) := by
  decide

lemma checked_94 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (94*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (94*256+l.val))) (certificate (94*256+l.val)) := by
  decide

lemma checked_95 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (95*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (95*256+l.val))) (certificate (95*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
