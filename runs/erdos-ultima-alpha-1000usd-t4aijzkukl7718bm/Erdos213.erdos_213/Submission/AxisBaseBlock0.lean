import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block0 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (0*64+hi.val) lo.val=true := by
  decide +kernel

theorem block1 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (1*64+hi.val) lo.val=true := by
  decide +kernel

theorem block2 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (2*64+hi.val) lo.val=true := by
  decide +kernel

theorem block3 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (3*64+hi.val) lo.val=true := by
  decide +kernel

theorem block4 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (4*64+hi.val) lo.val=true := by
  decide +kernel

theorem block5 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (5*64+hi.val) lo.val=true := by
  decide +kernel

theorem block6 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (6*64+hi.val) lo.val=true := by
  decide +kernel

theorem block7 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (7*64+hi.val) lo.val=true := by
  decide +kernel

theorem block8 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (8*64+hi.val) lo.val=true := by
  decide +kernel

theorem block9 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (9*64+hi.val) lo.val=true := by
  decide +kernel

theorem block10 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (10*64+hi.val) lo.val=true := by
  decide +kernel

theorem block11 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (11*64+hi.val) lo.val=true := by
  decide +kernel

theorem block12 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (12*64+hi.val) lo.val=true := by
  decide +kernel

theorem block13 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (13*64+hi.val) lo.val=true := by
  decide +kernel

theorem block14 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (14*64+hi.val) lo.val=true := by
  decide +kernel

theorem block15 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (15*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block15
end Erdos213.AxisBaseCompleteness
