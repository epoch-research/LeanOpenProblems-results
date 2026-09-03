import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block80 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (80*64+hi.val) lo.val=true := by
  decide +kernel

theorem block81 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (81*64+hi.val) lo.val=true := by
  decide +kernel

theorem block82 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (82*64+hi.val) lo.val=true := by
  decide +kernel

theorem block83 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (83*64+hi.val) lo.val=true := by
  decide +kernel

theorem block84 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (84*64+hi.val) lo.val=true := by
  decide +kernel

theorem block85 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (85*64+hi.val) lo.val=true := by
  decide +kernel

theorem block86 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (86*64+hi.val) lo.val=true := by
  decide +kernel

theorem block87 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (87*64+hi.val) lo.val=true := by
  decide +kernel

theorem block88 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (88*64+hi.val) lo.val=true := by
  decide +kernel

theorem block89 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (89*64+hi.val) lo.val=true := by
  decide +kernel

theorem block90 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (90*64+hi.val) lo.val=true := by
  decide +kernel

theorem block91 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (91*64+hi.val) lo.val=true := by
  decide +kernel

theorem block92 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (92*64+hi.val) lo.val=true := by
  decide +kernel

theorem block93 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (93*64+hi.val) lo.val=true := by
  decide +kernel

theorem block94 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (94*64+hi.val) lo.val=true := by
  decide +kernel

theorem block95 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (95*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block95
end Erdos213.AxisBaseCompleteness
