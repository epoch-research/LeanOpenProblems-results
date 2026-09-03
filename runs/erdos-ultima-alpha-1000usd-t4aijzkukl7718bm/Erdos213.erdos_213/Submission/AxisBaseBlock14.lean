import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block224 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (224*64+hi.val) lo.val=true := by
  decide +kernel

theorem block225 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (225*64+hi.val) lo.val=true := by
  decide +kernel

theorem block226 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (226*64+hi.val) lo.val=true := by
  decide +kernel

theorem block227 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (227*64+hi.val) lo.val=true := by
  decide +kernel

theorem block228 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (228*64+hi.val) lo.val=true := by
  decide +kernel

theorem block229 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (229*64+hi.val) lo.val=true := by
  decide +kernel

theorem block230 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (230*64+hi.val) lo.val=true := by
  decide +kernel

theorem block231 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (231*64+hi.val) lo.val=true := by
  decide +kernel

theorem block232 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (232*64+hi.val) lo.val=true := by
  decide +kernel

theorem block233 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (233*64+hi.val) lo.val=true := by
  decide +kernel

theorem block234 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (234*64+hi.val) lo.val=true := by
  decide +kernel

theorem block235 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (235*64+hi.val) lo.val=true := by
  decide +kernel

theorem block236 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (236*64+hi.val) lo.val=true := by
  decide +kernel

theorem block237 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (237*64+hi.val) lo.val=true := by
  decide +kernel

theorem block238 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (238*64+hi.val) lo.val=true := by
  decide +kernel

theorem block239 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (239*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block239
end Erdos213.AxisBaseCompleteness
