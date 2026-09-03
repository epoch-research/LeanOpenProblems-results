import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block384 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (384*64+hi.val) lo.val=true := by
  decide +kernel

theorem block385 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (385*64+hi.val) lo.val=true := by
  decide +kernel

theorem block386 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (386*64+hi.val) lo.val=true := by
  decide +kernel

theorem block387 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (387*64+hi.val) lo.val=true := by
  decide +kernel

theorem block388 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (388*64+hi.val) lo.val=true := by
  decide +kernel

theorem block389 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (389*64+hi.val) lo.val=true := by
  decide +kernel

theorem block390 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (390*64+hi.val) lo.val=true := by
  decide +kernel

theorem block391 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (391*64+hi.val) lo.val=true := by
  decide +kernel

theorem block392 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (392*64+hi.val) lo.val=true := by
  decide +kernel

theorem block393 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (393*64+hi.val) lo.val=true := by
  decide +kernel

theorem block394 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (394*64+hi.val) lo.val=true := by
  decide +kernel

theorem block395 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (395*64+hi.val) lo.val=true := by
  decide +kernel

theorem block396 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (396*64+hi.val) lo.val=true := by
  decide +kernel

theorem block397 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (397*64+hi.val) lo.val=true := by
  decide +kernel

theorem block398 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (398*64+hi.val) lo.val=true := by
  decide +kernel

theorem block399 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (399*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block399
end Erdos213.AxisBaseCompleteness
