import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block32 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (32*64+hi.val) lo.val=true := by
  decide +kernel

theorem block33 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (33*64+hi.val) lo.val=true := by
  decide +kernel

theorem block34 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (34*64+hi.val) lo.val=true := by
  decide +kernel

theorem block35 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (35*64+hi.val) lo.val=true := by
  decide +kernel

theorem block36 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (36*64+hi.val) lo.val=true := by
  decide +kernel

theorem block37 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (37*64+hi.val) lo.val=true := by
  decide +kernel

theorem block38 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (38*64+hi.val) lo.val=true := by
  decide +kernel

theorem block39 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (39*64+hi.val) lo.val=true := by
  decide +kernel

theorem block40 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (40*64+hi.val) lo.val=true := by
  decide +kernel

theorem block41 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (41*64+hi.val) lo.val=true := by
  decide +kernel

theorem block42 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (42*64+hi.val) lo.val=true := by
  decide +kernel

theorem block43 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (43*64+hi.val) lo.val=true := by
  decide +kernel

theorem block44 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (44*64+hi.val) lo.val=true := by
  decide +kernel

theorem block45 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (45*64+hi.val) lo.val=true := by
  decide +kernel

theorem block46 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (46*64+hi.val) lo.val=true := by
  decide +kernel

theorem block47 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (47*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block47
end Erdos213.AxisBaseCompleteness
