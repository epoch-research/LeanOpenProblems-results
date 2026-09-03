import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block16 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (16*64+hi.val) lo.val=true := by
  decide +kernel

theorem block17 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (17*64+hi.val) lo.val=true := by
  decide +kernel

theorem block18 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (18*64+hi.val) lo.val=true := by
  decide +kernel

theorem block19 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (19*64+hi.val) lo.val=true := by
  decide +kernel

theorem block20 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (20*64+hi.val) lo.val=true := by
  decide +kernel

theorem block21 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (21*64+hi.val) lo.val=true := by
  decide +kernel

theorem block22 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (22*64+hi.val) lo.val=true := by
  decide +kernel

theorem block23 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (23*64+hi.val) lo.val=true := by
  decide +kernel

theorem block24 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (24*64+hi.val) lo.val=true := by
  decide +kernel

theorem block25 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (25*64+hi.val) lo.val=true := by
  decide +kernel

theorem block26 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (26*64+hi.val) lo.val=true := by
  decide +kernel

theorem block27 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (27*64+hi.val) lo.val=true := by
  decide +kernel

theorem block28 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (28*64+hi.val) lo.val=true := by
  decide +kernel

theorem block29 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (29*64+hi.val) lo.val=true := by
  decide +kernel

theorem block30 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (30*64+hi.val) lo.val=true := by
  decide +kernel

theorem block31 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (31*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block31
end Erdos213.AxisBaseCompleteness
