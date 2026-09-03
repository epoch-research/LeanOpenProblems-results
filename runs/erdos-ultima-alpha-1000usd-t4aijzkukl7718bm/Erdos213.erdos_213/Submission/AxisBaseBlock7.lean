import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block112 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (112*64+hi.val) lo.val=true := by
  decide +kernel

theorem block113 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (113*64+hi.val) lo.val=true := by
  decide +kernel

theorem block114 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (114*64+hi.val) lo.val=true := by
  decide +kernel

theorem block115 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (115*64+hi.val) lo.val=true := by
  decide +kernel

theorem block116 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (116*64+hi.val) lo.val=true := by
  decide +kernel

theorem block117 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (117*64+hi.val) lo.val=true := by
  decide +kernel

theorem block118 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (118*64+hi.val) lo.val=true := by
  decide +kernel

theorem block119 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (119*64+hi.val) lo.val=true := by
  decide +kernel

theorem block120 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (120*64+hi.val) lo.val=true := by
  decide +kernel

theorem block121 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (121*64+hi.val) lo.val=true := by
  decide +kernel

theorem block122 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (122*64+hi.val) lo.val=true := by
  decide +kernel

theorem block123 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (123*64+hi.val) lo.val=true := by
  decide +kernel

theorem block124 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (124*64+hi.val) lo.val=true := by
  decide +kernel

theorem block125 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (125*64+hi.val) lo.val=true := by
  decide +kernel

theorem block126 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (126*64+hi.val) lo.val=true := by
  decide +kernel

theorem block127 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (127*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block127
end Erdos213.AxisBaseCompleteness
