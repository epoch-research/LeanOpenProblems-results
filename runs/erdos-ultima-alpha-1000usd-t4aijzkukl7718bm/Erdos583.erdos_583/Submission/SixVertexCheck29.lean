import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 29. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_116 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (116*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (116*256+l.val))) (certificate (116*256+l.val)) := by
  decide

lemma checked_117 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (117*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (117*256+l.val))) (certificate (117*256+l.val)) := by
  decide

lemma checked_118 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (118*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (118*256+l.val))) (certificate (118*256+l.val)) := by
  decide

lemma checked_119 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (119*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (119*256+l.val))) (certificate (119*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
