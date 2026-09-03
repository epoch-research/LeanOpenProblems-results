import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block256 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (256*64+hi.val) lo.val=true := by
  decide +kernel

theorem block257 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (257*64+hi.val) lo.val=true := by
  decide +kernel

theorem block258 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (258*64+hi.val) lo.val=true := by
  decide +kernel

theorem block259 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (259*64+hi.val) lo.val=true := by
  decide +kernel

theorem block260 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (260*64+hi.val) lo.val=true := by
  decide +kernel

theorem block261 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (261*64+hi.val) lo.val=true := by
  decide +kernel

theorem block262 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (262*64+hi.val) lo.val=true := by
  decide +kernel

theorem block263 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (263*64+hi.val) lo.val=true := by
  decide +kernel

theorem block264 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (264*64+hi.val) lo.val=true := by
  decide +kernel

theorem block265 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (265*64+hi.val) lo.val=true := by
  decide +kernel

theorem block266 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (266*64+hi.val) lo.val=true := by
  decide +kernel

theorem block267 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (267*64+hi.val) lo.val=true := by
  decide +kernel

theorem block268 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (268*64+hi.val) lo.val=true := by
  decide +kernel

theorem block269 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (269*64+hi.val) lo.val=true := by
  decide +kernel

theorem block270 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (270*64+hi.val) lo.val=true := by
  decide +kernel

theorem block271 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (271*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block271
end Erdos213.AxisBaseCompleteness
