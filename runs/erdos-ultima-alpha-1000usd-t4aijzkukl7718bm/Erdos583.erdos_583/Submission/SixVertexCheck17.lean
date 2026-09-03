import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 17. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_68 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (68*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (68*256+l.val))) (certificate (68*256+l.val)) := by
  decide

lemma checked_69 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (69*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (69*256+l.val))) (certificate (69*256+l.val)) := by
  decide

lemma checked_70 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (70*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (70*256+l.val))) (certificate (70*256+l.val)) := by
  decide

lemma checked_71 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (71*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (71*256+l.val))) (certificate (71*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
