import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 11. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_44 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (44*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (44*256+l.val))) (certificate (44*256+l.val)) := by
  decide

lemma checked_45 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (45*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (45*256+l.val))) (certificate (45*256+l.val)) := by
  decide

lemma checked_46 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (46*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (46*256+l.val))) (certificate (46*256+l.val)) := by
  decide

lemma checked_47 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (47*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (47*256+l.val))) (certificate (47*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
