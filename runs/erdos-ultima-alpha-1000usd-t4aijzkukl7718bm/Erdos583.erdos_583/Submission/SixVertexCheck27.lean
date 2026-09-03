import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 27. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_108 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (108*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (108*256+l.val))) (certificate (108*256+l.val)) := by
  decide

lemma checked_109 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (109*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (109*256+l.val))) (certificate (109*256+l.val)) := by
  decide

lemma checked_110 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (110*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (110*256+l.val))) (certificate (110*256+l.val)) := by
  decide

lemma checked_111 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (111*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (111*256+l.val))) (certificate (111*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
