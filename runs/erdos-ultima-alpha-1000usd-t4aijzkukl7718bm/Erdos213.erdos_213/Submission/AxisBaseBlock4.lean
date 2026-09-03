import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block64 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (64*64+hi.val) lo.val=true := by
  decide +kernel

theorem block65 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (65*64+hi.val) lo.val=true := by
  decide +kernel

theorem block66 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (66*64+hi.val) lo.val=true := by
  decide +kernel

theorem block67 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (67*64+hi.val) lo.val=true := by
  decide +kernel

theorem block68 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (68*64+hi.val) lo.val=true := by
  decide +kernel

theorem block69 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (69*64+hi.val) lo.val=true := by
  decide +kernel

theorem block70 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (70*64+hi.val) lo.val=true := by
  decide +kernel

theorem block71 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (71*64+hi.val) lo.val=true := by
  decide +kernel

theorem block72 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (72*64+hi.val) lo.val=true := by
  decide +kernel

theorem block73 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (73*64+hi.val) lo.val=true := by
  decide +kernel

theorem block74 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (74*64+hi.val) lo.val=true := by
  decide +kernel

theorem block75 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (75*64+hi.val) lo.val=true := by
  decide +kernel

theorem block76 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (76*64+hi.val) lo.val=true := by
  decide +kernel

theorem block77 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (77*64+hi.val) lo.val=true := by
  decide +kernel

theorem block78 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (78*64+hi.val) lo.val=true := by
  decide +kernel

theorem block79 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (79*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block79
end Erdos213.AxisBaseCompleteness
