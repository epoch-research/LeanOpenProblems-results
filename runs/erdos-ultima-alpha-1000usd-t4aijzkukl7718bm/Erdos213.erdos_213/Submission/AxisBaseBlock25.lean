import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block400 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (400*64+hi.val) lo.val=true := by
  decide +kernel

theorem block401 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (401*64+hi.val) lo.val=true := by
  decide +kernel

theorem block402 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (402*64+hi.val) lo.val=true := by
  decide +kernel

theorem block403 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (403*64+hi.val) lo.val=true := by
  decide +kernel

theorem block404 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (404*64+hi.val) lo.val=true := by
  decide +kernel

theorem block405 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (405*64+hi.val) lo.val=true := by
  decide +kernel

theorem block406 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (406*64+hi.val) lo.val=true := by
  decide +kernel

theorem block407 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (407*64+hi.val) lo.val=true := by
  decide +kernel

theorem block408 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (408*64+hi.val) lo.val=true := by
  decide +kernel

theorem block409 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (409*64+hi.val) lo.val=true := by
  decide +kernel

theorem block410 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (410*64+hi.val) lo.val=true := by
  decide +kernel

theorem block411 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (411*64+hi.val) lo.val=true := by
  decide +kernel

theorem block412 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (412*64+hi.val) lo.val=true := by
  decide +kernel

theorem block413 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (413*64+hi.val) lo.val=true := by
  decide +kernel

theorem block414 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (414*64+hi.val) lo.val=true := by
  decide +kernel

theorem block415 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (415*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block415
end Erdos213.AxisBaseCompleteness
