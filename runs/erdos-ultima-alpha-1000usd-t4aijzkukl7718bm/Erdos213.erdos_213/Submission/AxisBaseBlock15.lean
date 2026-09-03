import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block240 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (240*64+hi.val) lo.val=true := by
  decide +kernel

theorem block241 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (241*64+hi.val) lo.val=true := by
  decide +kernel

theorem block242 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (242*64+hi.val) lo.val=true := by
  decide +kernel

theorem block243 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (243*64+hi.val) lo.val=true := by
  decide +kernel

theorem block244 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (244*64+hi.val) lo.val=true := by
  decide +kernel

theorem block245 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (245*64+hi.val) lo.val=true := by
  decide +kernel

theorem block246 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (246*64+hi.val) lo.val=true := by
  decide +kernel

theorem block247 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (247*64+hi.val) lo.val=true := by
  decide +kernel

theorem block248 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (248*64+hi.val) lo.val=true := by
  decide +kernel

theorem block249 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (249*64+hi.val) lo.val=true := by
  decide +kernel

theorem block250 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (250*64+hi.val) lo.val=true := by
  decide +kernel

theorem block251 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (251*64+hi.val) lo.val=true := by
  decide +kernel

theorem block252 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (252*64+hi.val) lo.val=true := by
  decide +kernel

theorem block253 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (253*64+hi.val) lo.val=true := by
  decide +kernel

theorem block254 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (254*64+hi.val) lo.val=true := by
  decide +kernel

theorem block255 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (255*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block255
end Erdos213.AxisBaseCompleteness
