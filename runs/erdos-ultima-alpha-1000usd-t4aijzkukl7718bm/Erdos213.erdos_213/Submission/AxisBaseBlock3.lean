import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block48 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (48*64+hi.val) lo.val=true := by
  decide +kernel

theorem block49 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (49*64+hi.val) lo.val=true := by
  decide +kernel

theorem block50 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (50*64+hi.val) lo.val=true := by
  decide +kernel

theorem block51 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (51*64+hi.val) lo.val=true := by
  decide +kernel

theorem block52 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (52*64+hi.val) lo.val=true := by
  decide +kernel

theorem block53 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (53*64+hi.val) lo.val=true := by
  decide +kernel

theorem block54 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (54*64+hi.val) lo.val=true := by
  decide +kernel

theorem block55 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (55*64+hi.val) lo.val=true := by
  decide +kernel

theorem block56 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (56*64+hi.val) lo.val=true := by
  decide +kernel

theorem block57 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (57*64+hi.val) lo.val=true := by
  decide +kernel

theorem block58 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (58*64+hi.val) lo.val=true := by
  decide +kernel

theorem block59 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (59*64+hi.val) lo.val=true := by
  decide +kernel

theorem block60 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (60*64+hi.val) lo.val=true := by
  decide +kernel

theorem block61 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (61*64+hi.val) lo.val=true := by
  decide +kernel

theorem block62 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (62*64+hi.val) lo.val=true := by
  decide +kernel

theorem block63 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (63*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block63
end Erdos213.AxisBaseCompleteness
