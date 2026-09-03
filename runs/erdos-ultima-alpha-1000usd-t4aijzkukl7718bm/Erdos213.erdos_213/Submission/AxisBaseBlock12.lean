import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block192 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (192*64+hi.val) lo.val=true := by
  decide +kernel

theorem block193 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (193*64+hi.val) lo.val=true := by
  decide +kernel

theorem block194 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (194*64+hi.val) lo.val=true := by
  decide +kernel

theorem block195 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (195*64+hi.val) lo.val=true := by
  decide +kernel

theorem block196 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (196*64+hi.val) lo.val=true := by
  decide +kernel

theorem block197 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (197*64+hi.val) lo.val=true := by
  decide +kernel

theorem block198 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (198*64+hi.val) lo.val=true := by
  decide +kernel

theorem block199 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (199*64+hi.val) lo.val=true := by
  decide +kernel

theorem block200 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (200*64+hi.val) lo.val=true := by
  decide +kernel

theorem block201 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (201*64+hi.val) lo.val=true := by
  decide +kernel

theorem block202 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (202*64+hi.val) lo.val=true := by
  decide +kernel

theorem block203 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (203*64+hi.val) lo.val=true := by
  decide +kernel

theorem block204 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (204*64+hi.val) lo.val=true := by
  decide +kernel

theorem block205 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (205*64+hi.val) lo.val=true := by
  decide +kernel

theorem block206 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (206*64+hi.val) lo.val=true := by
  decide +kernel

theorem block207 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (207*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block207
end Erdos213.AxisBaseCompleteness
