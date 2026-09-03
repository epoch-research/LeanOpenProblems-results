import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 26. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_104 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (104*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (104*256+l.val))) (certificate (104*256+l.val)) := by
  decide

lemma checked_105 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (105*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (105*256+l.val))) (certificate (105*256+l.val)) := by
  decide

lemma checked_106 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (106*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (106*256+l.val))) (certificate (106*256+l.val)) := by
  decide

lemma checked_107 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (107*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (107*256+l.val))) (certificate (107*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
