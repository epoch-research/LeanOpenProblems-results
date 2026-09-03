import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block208 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (208*64+hi.val) lo.val=true := by
  decide +kernel

theorem block209 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (209*64+hi.val) lo.val=true := by
  decide +kernel

theorem block210 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (210*64+hi.val) lo.val=true := by
  decide +kernel

theorem block211 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (211*64+hi.val) lo.val=true := by
  decide +kernel

theorem block212 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (212*64+hi.val) lo.val=true := by
  decide +kernel

theorem block213 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (213*64+hi.val) lo.val=true := by
  decide +kernel

theorem block214 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (214*64+hi.val) lo.val=true := by
  decide +kernel

theorem block215 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (215*64+hi.val) lo.val=true := by
  decide +kernel

theorem block216 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (216*64+hi.val) lo.val=true := by
  decide +kernel

theorem block217 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (217*64+hi.val) lo.val=true := by
  decide +kernel

theorem block218 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (218*64+hi.val) lo.val=true := by
  decide +kernel

theorem block219 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (219*64+hi.val) lo.val=true := by
  decide +kernel

theorem block220 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (220*64+hi.val) lo.val=true := by
  decide +kernel

theorem block221 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (221*64+hi.val) lo.val=true := by
  decide +kernel

theorem block222 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (222*64+hi.val) lo.val=true := by
  decide +kernel

theorem block223 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (223*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block223
end Erdos213.AxisBaseCompleteness
