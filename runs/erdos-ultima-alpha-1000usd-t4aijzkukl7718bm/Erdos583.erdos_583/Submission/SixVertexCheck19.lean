import Submission.SixVertexCertificateData

/-! Kernel-checked certificate block 19. -/
namespace Erdos583SixVertexCertificatesDevelopment
open Erdos583SixVertexCodesDevelopment Erdos583SixVertexCertificateDataDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma checked_76 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (76*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (76*256+l.val))) (certificate (76*256+l.val)) := by
  decide

lemma checked_77 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (77*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (77*256+l.val))) (certificate (77*256+l.val)) := by
  decide

lemma checked_78 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (78*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (78*256+l.val))) (certificate (78*256+l.val)) := by
  decide

lemma checked_79 : ∀ l : Fin 256,
    Residual (BitVec.ofNat 15 (79*256+l.val)) →
      Valid (graph (BitVec.ofNat 15 (79*256+l.val))) (certificate (79*256+l.val)) := by
  decide

end Erdos583SixVertexCertificatesDevelopment
