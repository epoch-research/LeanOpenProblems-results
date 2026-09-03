import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 18. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_72 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (72*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (72*256+l.val))) (certificate (72*256+l.val)) := by
  decide

lemma checked_73 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (73*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (73*256+l.val))) (certificate (73*256+l.val)) := by
  decide

lemma checked_74 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (74*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (74*256+l.val))) (certificate (74*256+l.val)) := by
  decide

lemma checked_75 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (75*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (75*256+l.val))) (certificate (75*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
