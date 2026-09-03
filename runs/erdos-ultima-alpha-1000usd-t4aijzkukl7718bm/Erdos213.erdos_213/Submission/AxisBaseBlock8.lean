import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block128 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (128*64+hi.val) lo.val=true := by
  decide +kernel

theorem block129 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (129*64+hi.val) lo.val=true := by
  decide +kernel

theorem block130 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (130*64+hi.val) lo.val=true := by
  decide +kernel

theorem block131 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (131*64+hi.val) lo.val=true := by
  decide +kernel

theorem block132 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (132*64+hi.val) lo.val=true := by
  decide +kernel

theorem block133 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (133*64+hi.val) lo.val=true := by
  decide +kernel

theorem block134 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (134*64+hi.val) lo.val=true := by
  decide +kernel

theorem block135 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (135*64+hi.val) lo.val=true := by
  decide +kernel

theorem block136 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (136*64+hi.val) lo.val=true := by
  decide +kernel

theorem block137 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (137*64+hi.val) lo.val=true := by
  decide +kernel

theorem block138 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (138*64+hi.val) lo.val=true := by
  decide +kernel

theorem block139 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (139*64+hi.val) lo.val=true := by
  decide +kernel

theorem block140 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (140*64+hi.val) lo.val=true := by
  decide +kernel

theorem block141 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (141*64+hi.val) lo.val=true := by
  decide +kernel

theorem block142 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (142*64+hi.val) lo.val=true := by
  decide +kernel

theorem block143 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (143*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block143
end Erdos213.AxisBaseCompleteness
