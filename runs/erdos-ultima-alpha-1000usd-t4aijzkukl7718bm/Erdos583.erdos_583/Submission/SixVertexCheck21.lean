import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 21. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_84 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (84*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (84*256+l.val))) (certificate (84*256+l.val)) := by
  decide

lemma checked_85 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (85*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (85*256+l.val))) (certificate (85*256+l.val)) := by
  decide

lemma checked_86 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (86*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (86*256+l.val))) (certificate (86*256+l.val)) := by
  decide

lemma checked_87 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (87*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (87*256+l.val))) (certificate (87*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
