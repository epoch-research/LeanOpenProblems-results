import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block96 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (96*64+hi.val) lo.val=true := by
  decide +kernel

theorem block97 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (97*64+hi.val) lo.val=true := by
  decide +kernel

theorem block98 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (98*64+hi.val) lo.val=true := by
  decide +kernel

theorem block99 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (99*64+hi.val) lo.val=true := by
  decide +kernel

theorem block100 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (100*64+hi.val) lo.val=true := by
  decide +kernel

theorem block101 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (101*64+hi.val) lo.val=true := by
  decide +kernel

theorem block102 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (102*64+hi.val) lo.val=true := by
  decide +kernel

theorem block103 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (103*64+hi.val) lo.val=true := by
  decide +kernel

theorem block104 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (104*64+hi.val) lo.val=true := by
  decide +kernel

theorem block105 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (105*64+hi.val) lo.val=true := by
  decide +kernel

theorem block106 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (106*64+hi.val) lo.val=true := by
  decide +kernel

theorem block107 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (107*64+hi.val) lo.val=true := by
  decide +kernel

theorem block108 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (108*64+hi.val) lo.val=true := by
  decide +kernel

theorem block109 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (109*64+hi.val) lo.val=true := by
  decide +kernel

theorem block110 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (110*64+hi.val) lo.val=true := by
  decide +kernel

theorem block111 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (111*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block111
end Erdos213.AxisBaseCompleteness
